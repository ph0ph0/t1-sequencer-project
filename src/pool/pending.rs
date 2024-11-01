//! Pending transaction management for the transaction pool.
//!
//! This module contains structures and implementations for handling pending transactions
//! within the transaction pool. It provides functionality for creating, storing, and
//! managing transactions that are waiting to be included in a block.
//!

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use alloy::{
    consensus::{Transaction, TxEnvelope},
    primitives::Address,
};

use crate::{
    identifiers::TransactionId,
    ordering::{Priority, TransactionOrdering},
    pool::sequence::{TransactionSequence, TransactionSequenceFilter},
};

/// A transaction that is pending inclusion in a block
pub struct PendingTransaction<O>
where
    O: TransactionOrdering,
{
    /// The id of the submission that added this transaction to the pool
    submission_id: u64,
    /// The transaction
    transaction: Arc<TxEnvelope>,
    /// The priority of the transaction, used for ordering
    priority: Priority<O::PriorityValue>,
    /// The sender of the transaction
    sender: Address,
}

impl<O> PendingTransaction<O>
where
    O: TransactionOrdering,
{
    /// Creates a new `PendingTransaction`.
    pub fn new(
        submission_id: u64,
        transaction: Arc<TxEnvelope>,
        priority: Priority<O::PriorityValue>,
        sender: Address,
    ) -> Self {
        Self {
            submission_id,
            transaction,
            priority,
            sender,
        }
    }

    /// Returns a reference to the transaction.
    pub fn transaction(&self) -> &Arc<TxEnvelope> {
        &self.transaction
    }

    /// Returns the sender of the transaction.
    pub fn sender(&self) -> Address {
        self.sender
    }

    /// Returns the priority of the transaction.
    pub fn priority(&self) -> &Priority<O::PriorityValue> {
        &self.priority
    }

    /// The next transaction of the sender: `nonce + 1`
    pub(crate) fn unlocks(&self) -> TransactionId {
        TransactionId::new(self.sender, self.transaction.nonce() + 1)
    }
}

impl<O> Ord for PendingTransaction<O>
where
    O: TransactionOrdering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        // Primary sort by priority fee (ascending, best txs are at the end)
        self.priority
            .cmp(&other.priority)
            // Secondary sort by address
            .then(self.sender.cmp(&other.sender))
    }
}

impl<O> PartialOrd for PendingTransaction<O>
where
    O: TransactionOrdering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<O> Eq for PendingTransaction<O> where O: TransactionOrdering {}

impl<O> PartialEq<Self> for PendingTransaction<O>
where
    O: TransactionOrdering,
{
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<O: TransactionOrdering> Clone for PendingTransaction<O>
where
    O: TransactionOrdering,
{
    fn clone(&self) -> Self {
        Self {
            submission_id: self.submission_id,
            transaction: Arc::clone(&self.transaction),
            priority: self.priority.clone(),
            sender: self.sender,
        }
    }
}

impl<O> std::fmt::Debug for PendingTransaction<O>
where
    O: TransactionOrdering,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PendingTransaction")
            .field("submission_id", &self.submission_id)
            .field("transaction", &self.transaction)
            .field("priority", &self.priority)
            .field("sender", &self.sender)
            .finish()
    }
}

/// A pool that manages pending transactions.
///
/// The `PendingPool` maintains multiple data structures to efficiently track and order transactions:
///
/// - `by_id`: Maps transaction IDs to their corresponding `PendingTransaction` wrappers
/// - `all`: A sorted set of all transactions ordered by priority
/// - `independent_transactions`: A sorted set of transactions that can be executed independently (no dependencies)
/// - `highest_nonces`: A sorted set tracking the highest nonce transaction for each sender
///
/// The pool ensures transactions are gapless (no nonce gaps) and maintains proper ordering based on the
/// provided `TransactionOrdering` implementation.
///
/// # Type Parameters
///
/// * `O` - The transaction ordering strategy that implements `TransactionOrdering`

#[derive(Debug, Clone)]
pub struct PendingPool<O>
where
    O: TransactionOrdering,
{
    /// Determines how the transactions will be ordered
    ordering: O,
    /// Assigned to each tx, used to determine when transactions were added to the pool
    submission_id: u64,
    /// All the transactions in the pool grouped by their sender and ordered by nonce
    by_id: BTreeMap<TransactionId, PendingTransaction<O>>,
    /// All transactions sorted by priority
    all: BTreeSet<PendingTransaction<O>>,
    /// Independent transactions that can be included directly and don't require other
    /// transactions.
    ///
    /// Sorted by their scoring value.
    independent_transactions: BTreeSet<PendingTransaction<O>>,
    /// The highest nonce transactions for each sender - like the `independent` set, but the
    /// highest instead of lowest nonce.
    ///
    /// Sorted by their scoring value.
    highest_nonces: BTreeSet<PendingTransaction<O>>,
}

impl<O> PendingPool<O>
where
    O: TransactionOrdering,
{
    /// Creates a new `PendingPool` with the given ordering strategy.
    pub fn new(ordering: O) -> Self {
        Self {
            ordering,
            submission_id: 0,
            by_id: BTreeMap::default(),
            all: BTreeSet::default(),
            independent_transactions: BTreeSet::default(),
            highest_nonces: BTreeSet::default(),
        }
    }

    /// Retrieves a transaction with the given ID from the pool, if it exists.
    pub fn get(&self, id: &TransactionId) -> Option<&PendingTransaction<O>> {
        self.by_id.get(id)
    }

    /// Returns the ancestor the given transaction, the transaction with `nonce - 1`.
    ///
    /// Note: for a transaction with nonce higher than the current on chain nonce this will always
    /// return an ancestor since all transaction in this pool are gapless.
    fn ancestor(&self, id: &TransactionId) -> Option<&PendingTransaction<O>> {
        self.get(&id.unchecked_ancestor()?)
    }

    /// Returns `true` if the transaction with the given id is already included in this pool.
    pub(crate) fn contains(&self, id: &TransactionId) -> bool {
        self.by_id.contains_key(id)
    }

    /// Returns the next submission id in the [PendingPool]
    fn next_id(&mut self) -> u64 {
        let id = self.submission_id;
        self.submission_id = self.submission_id.wrapping_add(1);
        id
    }

    /// Adds a new transaction to the pending queue.
    ///
    /// # Panics
    ///
    /// if the transaction is already included
    pub(crate) fn add_transaction(&mut self, tx: Arc<TxEnvelope>, base_fee: u64) {
        let sender = tx.recover_signer().unwrap();
        let tx_id = TransactionId::new(sender, tx.nonce());

        assert!(
            !self.contains(&tx_id),
            "transaction already included {:?}",
            self.get(&tx_id).unwrap().transaction
        );

        let submission_id = self.next_id();
        let priority = self.ordering.priority(&tx, base_fee);
        let tx = PendingTransaction {
            submission_id,
            transaction: tx,
            priority,
            sender,
        };

        self.update_independents_and_highest_nonces(&tx, &tx_id);
        self.all.insert(tx.clone());

        self.by_id.insert(tx_id, tx);
    }

    /// Updates the independent transaction and highest nonces set, assuming the given transaction
    /// is being _added_ to the pool.
    fn update_independents_and_highest_nonces(
        &mut self,
        tx: &PendingTransaction<O>,
        tx_id: &TransactionId,
    ) {
        let ancestor_id = tx_id.unchecked_ancestor();
        if let Some(ancestor) = ancestor_id.and_then(|id| self.by_id.get(&id)) {
            // the transaction already has an ancestor, so we only need to ensure that the
            // highest nonces set actually contains the highest nonce for that sender
            self.highest_nonces.remove(ancestor);
        } else {
            // If there's __no__ ancestor in the pool, then this transaction is independent, this is
            // guaranteed because this pool is gapless.
            self.independent_transactions.insert(tx.clone());
        }
        self.highest_nonces.insert(tx.clone());
    }

    /// Removes the transaction from the pool.
    ///
    /// Note: If the transaction has a descendant transaction
    /// it will advance it to the best queue.
    pub(crate) fn remove_transaction(&mut self, id: &TransactionId) -> Option<Arc<TxEnvelope>> {
        // mark the next as independent if it exists
        if let Some(unlocked) = self.get(&id.descendant()) {
            self.independent_transactions.insert(unlocked.clone());
        }
        let tx = self.by_id.remove(id)?;
        self.all.remove(&tx);
        self.independent_transactions.remove(&tx);

        // switch out for the next ancestor if there is one (ie next highest nonce)
        if self.highest_nonces.remove(&tx) {
            if let Some(ancestor) = self.ancestor(id) {
                self.highest_nonces.insert(ancestor.clone());
            }
        }
        Some(tx.transaction)
    }

    /// Returns the transaction sequence iterator
    pub(crate) fn transaction_sequence(&self) -> TransactionSequence<O> {
        TransactionSequence {
            all: self.by_id.clone(),
            independent: self.independent_transactions.clone(),
            invalid: Default::default(),
        }
    }

    /// Returns the filtered transaction sequence iterator
    pub fn filter_sequence(
        &self,
        predicate: Box<dyn FnMut(&<TransactionSequence<O> as Iterator>::Item) -> bool>,
    ) -> TransactionSequenceFilter<O> {
        let transaction_sequence = self.transaction_sequence();
        TransactionSequenceFilter::new(transaction_sequence, predicate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordering::CoinbaseTipOrdering;
    use crate::test_utils::helpers::{
        create_default_tx_and_sender, create_tx, create_tx_and_sender,
    };
    use alloy::primitives::U256;

    #[tokio::test]
    async fn test_add_and_remove_transaction() {
        let mut pool =
            PendingPool::<CoinbaseTipOrdering<TxEnvelope>>::new(CoinbaseTipOrdering::default());
        let (tx, _, _) = create_default_tx_and_sender().await;
        let tx_id = TransactionId::from(Arc::clone(&tx));

        // Insert transaction
        pool.add_transaction(Arc::clone(&tx), 10);

        // Check if transaction is in the pool
        assert!(pool.contains(&tx_id));
        assert_eq!(pool.by_id.len(), 1);
        assert_eq!(pool.all.len(), 1);
        assert_eq!(pool.independent_transactions.len(), 1);
        assert_eq!(pool.highest_nonces.len(), 1);

        // Remove transaction
        let removed_tx = pool.remove_transaction(&tx_id);
        assert_eq!(removed_tx, Some(tx));
        assert_eq!(pool.by_id.len(), 0);
        assert_eq!(pool.all.len(), 0);
        assert_eq!(pool.independent_transactions.len(), 0);
        assert_eq!(pool.highest_nonces.len(), 0);
        assert!(!pool.contains(&tx_id));
    }

    #[tokio::test]
    async fn test_remove_transaction_with_descendant() {
        let mut pool =
            PendingPool::<CoinbaseTipOrdering<TxEnvelope>>::new(CoinbaseTipOrdering::default());
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key, sender, 15, 25, 100000, U256::ZERO, 1).await;

        pool.add_transaction(Arc::clone(&tx1), 10);
        pool.add_transaction(Arc::clone(&tx2), 10);

        let tx1_id = TransactionId::from(Arc::clone(&tx1));
        pool.remove_transaction(&tx1_id);

        assert_eq!(pool.independent_transactions.len(), 1);
        let independent_tx = pool.independent_transactions.iter().next().unwrap();
        assert_eq!(independent_tx.transaction.nonce(), 1);
    }

    #[tokio::test]
    async fn test_ancestor() {
        // Create a pool
        let mut pool =
            PendingPool::<CoinbaseTipOrdering<TxEnvelope>>::new(CoinbaseTipOrdering::default());
        // Create transactions
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key.clone(), sender, 15, 25, 100000, U256::ZERO, 1).await;
        let tx3 = create_tx(private_key.clone(), sender, 20, 30, 100000, U256::ZERO, 2).await;

        // Create PendingTransactions
        let tx1_pending = PendingTransaction {
            submission_id: pool.next_id(),
            transaction: Arc::clone(&tx1),
            priority: pool.ordering.priority(&tx1, 10),
            sender,
        };

        let tx2_pending: PendingTransaction<CoinbaseTipOrdering<TxEnvelope>> = PendingTransaction {
            submission_id: pool.next_id(),
            transaction: Arc::clone(&tx2),
            priority: pool.ordering.priority(&tx2, 10),
            sender,
        };

        // Add transactions to the pool
        pool.add_transaction(Arc::clone(&tx1), 10); // nonce 0
        pool.add_transaction(Arc::clone(&tx2), 10); // nonce 1
        pool.add_transaction(Arc::clone(&tx3), 10); // nonce 2

        let tx1_id = TransactionId::from(Arc::clone(&tx1));
        let tx2_id = TransactionId::from(Arc::clone(&tx2));
        let tx3_id = TransactionId::from(Arc::clone(&tx3));

        // Test ancestor of tx2
        assert_eq!(pool.ancestor(&tx2_id), Some(&tx1_pending));

        // Test ancestor of tx3
        assert_eq!(pool.ancestor(&tx3_id), Some(&tx2_pending));

        // Test ancestor of tx1 (should be None)
        assert_eq!(pool.ancestor(&tx1_id), None);
    }

    #[tokio::test]
    async fn test_ordering() {
        // Tests the ordering of transactions in the pool. We expect the transactions with the highest effective tip to be at the end of the sequence,
        // since we pop from the end of the sequence during execution.
        let mut pool =
            PendingPool::<CoinbaseTipOrdering<TxEnvelope>>::new(CoinbaseTipOrdering::default());

        // effective tip = min(max_fee_per_gas - base_fee, max_priority_fee_per_gas)
        // effective tx1_tip = min(10 - 1, 20) = 9
        let (tx1, sender1, _) = create_default_tx_and_sender().await;
        // effective tx2_tip2 = min(20 - 1, 30) = 19
        let (tx2, sender2, _) = create_tx_and_sender(20, 30, 100000, U256::ZERO, 0).await;
        // effective tx3_tip = min(30 - 1, 40) = 29
        let (tx3, sender3, _) = create_tx_and_sender(30, 40, 100000, U256::ZERO, 0).await; // max_fee_per_gas = 30
                                                                                           // effective tx4_tip = min(40 - 1, 50) = 39
        let (tx4, sender4, _) = create_tx_and_sender(40, 50, 100000, U256::ZERO, 0).await; // max_fee_per_gas = 40

        pool.add_transaction(Arc::clone(&tx4), 1);
        pool.add_transaction(Arc::clone(&tx2), 1);

        let ordered_txs: Vec<_> = pool.independent_transactions.iter().collect();
        assert_eq!(ordered_txs[0].sender, sender2);
        assert_eq!(ordered_txs[0].transaction.max_fee_per_gas(), 20);
        assert_eq!(ordered_txs[0].priority, Priority::Value(U256::from(19)));
        assert_eq!(ordered_txs[1].sender, sender4);
        assert_eq!(ordered_txs[1].transaction.max_fee_per_gas(), 40);
        assert_eq!(ordered_txs[1].priority, Priority::Value(U256::from(39)));

        // Add some more transactions

        pool.add_transaction(Arc::clone(&tx3), 1);
        pool.add_transaction(Arc::clone(&tx1), 1);

        // Check ordering with new transactions present
        let ordered_txs: Vec<_> = pool.independent_transactions.iter().collect();

        // Reorganize assert statements to reflect the smallest max_fee_per_gas first
        assert_eq!(ordered_txs[0].sender, sender1);
        assert_eq!(ordered_txs[0].transaction.max_fee_per_gas(), 10);
        assert_eq!(ordered_txs[0].priority, Priority::Value(U256::from(9)));
        assert_eq!(ordered_txs[1].sender, sender2);
        assert_eq!(ordered_txs[1].transaction.max_fee_per_gas(), 20);
        assert_eq!(ordered_txs[1].priority, Priority::Value(U256::from(19)));
        assert_eq!(ordered_txs[2].sender, sender3);
        assert_eq!(ordered_txs[2].transaction.max_fee_per_gas(), 30);
        assert_eq!(ordered_txs[2].priority, Priority::Value(U256::from(29)));
        assert_eq!(ordered_txs[3].sender, sender4);
        assert_eq!(ordered_txs[3].transaction.max_fee_per_gas(), 40);
        assert_eq!(ordered_txs[3].priority, Priority::Value(U256::from(39)));
    }
}
