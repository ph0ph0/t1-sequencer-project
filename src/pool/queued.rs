//! Queued transaction pool implementation.
//!
//! This module contains the implementation of a queued transaction pool,
//! which manages transactions in a priority queue based on their gas price
//! and submission order.
//!
//! The main structures in this module are:
//! - `QueuedPoolTransaction`: Represents a transaction in the pool with its submission order.
//! - `QueuedOrderedTransaction`: Represents an ordered transaction (implementation not shown in this snippet).
//!
//! The module also provides implementations for various traits like `Ord`, `PartialOrd`, `Eq`, and
//! `PartialEq` to enable efficient sorting and comparison.

use std::{
    cmp::Ordering,
    collections::{hash_map::Entry as HashMapEntry, BTreeMap, BTreeSet, HashMap},
    fmt::{self, Debug},
    sync::Arc,
};

use alloy::{
    consensus::{Transaction, TxEnvelope},
    primitives::Address,
};

use crate::identifiers::{SenderTransactionCount, TransactionId};

#[derive(PartialOrd, Eq, PartialEq, Debug)]
pub struct QueuedPoolTransaction {
    /// Id to indicate when transaction was added to pool
    submission_id: u64,
    /// The transaction
    transaction: QueuedOrderedTransaction,
}

impl Ord for QueuedPoolTransaction {
    fn cmp(&self, other: &Self) -> Ordering {
        // First, compare transactions by their own Ord impl (see `impl Ord for QueuedOrderedTransaction`)
        // Then compare the submission_ids.
        self.transaction
            .cmp(&other.transaction)
            .then_with(|| other.submission_id.cmp(&self.submission_id))
    }
}

impl Clone for QueuedPoolTransaction {
    fn clone(&self) -> Self {
        Self {
            submission_id: self.submission_id,
            transaction: self.transaction.clone(),
        }
    }
}

impl From<Arc<TxEnvelope>> for QueuedOrderedTransaction {
    fn from(tx: Arc<TxEnvelope>) -> Self {
        Self(tx)
    }
}

/// Type wrapper for an alloy TxEnvelope in the queue, allowing them to be ordered by max_fee_per_gas then submission_id (see Ord implemntation below)
pub struct QueuedOrderedTransaction(Arc<TxEnvelope>);

impl QueuedOrderedTransaction {
    /// Returns the max_fee_per_gas of the transaction
    pub fn max_fee_per_gas(&self) -> u128 {
        self.0.max_fee_per_gas()
    }
}

impl Ord for QueuedOrderedTransaction {
    // Sort in descending order (ie higher gas fees towards end of set)
    fn cmp(&self, other: &Self) -> Ordering {
        other.max_fee_per_gas().cmp(&self.max_fee_per_gas())
    }
}

impl PartialOrd for QueuedOrderedTransaction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for QueuedOrderedTransaction {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for QueuedOrderedTransaction {}

impl Clone for QueuedOrderedTransaction {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl Debug for QueuedOrderedTransaction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "QueuedOrderedTransaction({:?})", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct QueuedPool {
    /// Keeps track of the last transaction submitted to the pool
    current_submission_id: u64,
    /// All transaction currently inside the pool grouped by sender and ordered by nonce
    by_id: BTreeMap<TransactionId, QueuedPoolTransaction>,
    /// All transactions sorted by their order function. The higher the better.
    ///
    /// These are the transactions that could be promoted to pending
    best: BTreeSet<QueuedPoolTransaction>,

    /// Keeps track of the number of transactions in the pool by the sender and the last submission id.
    sender_transaction_count: HashMap<Address, SenderTransactionCount>,
}

impl QueuedPool {
    /// Returns `true` if the transaction with the given id is already included in this pool.
    pub(crate) fn contains(&self, id: &TransactionId) -> bool {
        self.by_id.contains_key(id)
    }

    /// Retrieves a transaction with the given ID from the pool, if it exists.
    fn get(&self, id: &TransactionId) -> Option<&QueuedPoolTransaction> {
        self.by_id.get(id)
    }

    /// Returns the next submission id
    fn next_id(&mut self) -> u64 {
        let id = self.current_submission_id;
        self.current_submission_id = self.current_submission_id.wrapping_add(1);
        id
    }

    /// Adds a new transactions to the pending queue.
    ///
    /// # Panics
    ///
    /// If the transaction is already included.
    pub(crate) fn add_transaction(&mut self, tx: Arc<TxEnvelope>) {
        let sender = tx.recover_signer().unwrap();
        let id = TransactionId::new(sender, tx.nonce());
        assert!(
            !self.contains(&id),
            "transaction already included {:?}",
            self.get(&id).unwrap().transaction
        );
        let submission_id = self.next_id();

        // update or create sender entry
        self.add_sender_count(sender, submission_id);
        let transaction = QueuedPoolTransaction {
            submission_id,
            transaction: tx.into(),
        };

        self.by_id.insert(id, transaction.clone());
        self.best.insert(transaction);
    }

    /// Increments the count of transactions for the given sender and updates the tracked submission
    /// id.
    fn add_sender_count(&mut self, sender: Address, submission_id: u64) {
        match self.sender_transaction_count.entry(sender) {
            HashMapEntry::Occupied(mut entry) => {
                let value = entry.get_mut();

                value.count += 1;
                value.last_submission_id = submission_id;
            }
            HashMapEntry::Vacant(entry) => {
                entry.insert(SenderTransactionCount {
                    count: 1,
                    last_submission_id: submission_id,
                });
            }
        }
    }

    /// Removes a transaction from the pool and returns the transaction.
    pub(crate) fn remove_transaction(&mut self, id: &TransactionId) -> Option<Arc<TxEnvelope>> {
        let tx = self.by_id.remove(id)?;
        self.best.remove(&tx);
        self.remove_sender_count(tx.transaction.0.recover_signer().unwrap());
        Some(tx.transaction.0.into())
    }

    /// Removes a sender count from the pool.
    fn remove_sender_count(&mut self, sender: Address) {
        match self.sender_transaction_count.entry(sender) {
            HashMapEntry::Occupied(mut entry) => {
                let value = entry.get_mut();
                value.count -= 1;
                if value.count == 0 {
                    entry.remove()
                } else {
                    return;
                }
            }
            HashMapEntry::Vacant(_) => {
                // This should never happen because the bisection between the two maps
                unreachable!("sender count not found {:?}", sender);
            }
        };
    }
}

impl Default for QueuedPool {
    fn default() -> Self {
        Self {
            current_submission_id: 0,
            by_id: BTreeMap::default(),
            best: BTreeSet::default(),
            sender_transaction_count: HashMap::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::helpers::{
        create_default_tx_and_sender, create_tx, create_tx_and_sender,
    };
    use alloy::primitives::U256;

    #[tokio::test]
    async fn test_add_transaction() {
        let mut pool = QueuedPool::default();
        let (tx, sender, _) = create_default_tx_and_sender().await;

        pool.add_transaction(tx.clone());

        assert_eq!(pool.by_id.len(), 1);
        assert_eq!(pool.best.len(), 1);
        assert_eq!(pool.sender_transaction_count.len(), 1);
        assert_eq!(pool.sender_transaction_count[&sender].count, 1);
    }

    #[tokio::test]
    async fn test_remove_transaction() {
        let mut pool = QueuedPool::default();
        let (tx, _, _) = create_default_tx_and_sender().await;
        let id = TransactionId::from(tx.clone());

        pool.add_transaction(tx.clone());
        let removed_tx = pool.remove_transaction(&id);

        assert!(removed_tx.is_some());
        assert_eq!(pool.by_id.len(), 0);
        assert_eq!(pool.best.len(), 0);
        assert_eq!(pool.sender_transaction_count.len(), 0);
    }

    #[tokio::test]
    async fn test_transaction_ordering() {
        let mut pool = QueuedPool::default();
        let (tx1, _, _) = create_default_tx_and_sender().await; // max_fee_per_gas = 10
        let (tx2, _, _) = create_tx_and_sender(20, 30, 100000, U256::ZERO, 0).await; // max_fee_per_gas = 20

        // Add transactions to the pool
        pool.add_transaction(tx1.clone());
        pool.add_transaction(tx2.clone());

        let ordered_txs: Vec<_> = pool.best.iter().collect();
        assert_eq!(ordered_txs.len(), 2);
        assert_eq!(ordered_txs[0].transaction.0.max_fee_per_gas(), 20);
        assert_eq!(ordered_txs[1].transaction.0.max_fee_per_gas(), 10);

        // Add some more transactions
        let (tx3, _, _) = create_tx_and_sender(30, 40, 100000, U256::ZERO, 0).await; // max_fee_per_gas = 30
        let (tx4, _, _) = create_tx_and_sender(40, 50, 100000, U256::ZERO, 0).await; // max_fee_per_gas = 40

        pool.add_transaction(tx3.clone());
        pool.add_transaction(tx4.clone());

        let ordered_txs: Vec<_> = pool.best.iter().collect();
        assert_eq!(ordered_txs.len(), 4);
        assert_eq!(ordered_txs[0].transaction.0.max_fee_per_gas(), 40);
        assert_eq!(ordered_txs[1].transaction.0.max_fee_per_gas(), 30);
        assert_eq!(ordered_txs[2].transaction.0.max_fee_per_gas(), 20);
        assert_eq!(ordered_txs[3].transaction.0.max_fee_per_gas(), 10);
    }

    #[tokio::test]
    async fn test_sender_transaction_count() {
        let mut pool = QueuedPool::default();
        let (tx1, sender1, pk1) = create_default_tx_and_sender().await;
        let (tx2, sender2, pk2) = create_tx_and_sender(20, 30, 100000, U256::ZERO, 0).await;
        let tx3 = create_tx(pk1, sender1, 30, 40, 100000, U256::ZERO, 1).await;
        let tx4 = create_tx(pk2, sender2, 40, 50, 100000, U256::ZERO, 1).await;

        // Add transactions to the pool
        pool.add_transaction(tx1.clone());
        pool.add_transaction(tx2.clone());
        pool.add_transaction(tx3.clone());
        pool.add_transaction(tx4.clone());

        // Check sender counts are all 2
        assert_eq!(pool.sender_transaction_count[&sender1].count, 2);
        assert_eq!(pool.sender_transaction_count[&sender2].count, 2);

        // Remove tx1 from the pool
        let id1 = TransactionId::from(tx1.clone());
        pool.remove_transaction(&id1);

        // Sender1 should now have 1 transaction
        assert_eq!(pool.sender_transaction_count[&sender1].count, 1);

        // Remove tx2 from the pool
        let id2 = TransactionId::from(tx2.clone());
        pool.remove_transaction(&id2);

        // Sender2 should now have 1 transaction
        assert_eq!(pool.sender_transaction_count[&sender2].count, 1);

        // Remove tx3 from the pool
        let id3 = TransactionId::from(tx3.clone());
        pool.remove_transaction(&id3);

        // Sender1 should now have 0 transactions
        assert!(!pool.sender_transaction_count.contains_key(&sender1));

        // Remove tx4 from the pool
        let id4 = TransactionId::from(tx4.clone());
        pool.remove_transaction(&id4);

        // Sender2 should now have 0 transactions
        assert!(!pool.sender_transaction_count.contains_key(&sender2));
    }
}
