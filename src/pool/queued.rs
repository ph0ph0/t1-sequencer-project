
// -----queued.rs-----

use std::{
    cmp::Ordering,
    collections::{
        BTreeMap, 
        BTreeSet, 
        HashMap, 
        hash_map::Entry as HashMapEntry
    },
    fmt::{self, Debug},
    sync::Arc,
};

use alloy::{
    consensus::{TxEnvelope, Transaction},
    primitives::Address,
};

use crate::identifiers::{TransactionId, SenderTransactionCount};


#[derive(PartialOrd, Eq, PartialEq, Debug)]
pub struct QueuedPoolTransaction {

    /// Id to indicate when transaction was added to pool
    submission_id: u64,
    /// The transaction
    transaction: QueuedOrderedTransaction
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
            transaction: self.transaction.clone()
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
    pub fn max_fee_per_gas(&self) -> u128 {
        self.0.max_fee_per_gas()
    }
}

impl Ord for QueuedOrderedTransaction {
    // Sort in reverse order (ie higher gas fees towards end of set)
    fn cmp(&self, other: &Self) -> Ordering {
        other.max_fee_per_gas()
            .cmp(&self.max_fee_per_gas())
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


// TODO: Derive
pub struct QueuedPool {
    /// Keeps track of the last transaction submitted to the pool
    current_submission_id: u64,
    /// All transaction currently inside the pool grouped by sender and ordered by nonce
    by_id: BTreeMap<TransactionId, QueuedPoolTransaction>,
    /// All transactions sorted by their order function. The higher the better.
    best: BTreeSet<QueuedPoolTransaction>,

    /// Last submission_id for each sender, TODO: Do we need this?
    // last_sender_submission: BTreeSet<SubmissionSenderId>>,

    // TODO: Move up to Pool?
    // Keeps track of the number of transactions in the pool by the sender and the last submission id.
    sender_transaction_count: HashMap<Address, SenderTransactionCount>
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
        let transaction = QueuedPoolTransaction { submission_id, transaction: tx.into() };

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
                entry
                    .insert(SenderTransactionCount { count: 1, last_submission_id: submission_id });
            }
        }
    }

    pub(crate) fn remove_transaction(&mut self, id: &TransactionId) -> Option<Arc<TxEnvelope>> {
        let tx = self.by_id.remove(id)?;
        self.best.remove(&tx);
        self.remove_sender_count(tx.transaction.0.recover_signer().unwrap());
        Some(tx.transaction.0.into())
    }

    fn remove_sender_count(&mut self, sender: Address) {
        match self.sender_transaction_count.entry(sender) {
            HashMapEntry::Occupied(mut entry) => {
                let value = entry.get_mut();
                value.count -= 1;
                if value.count == 0 {
                    entry.remove()
                } else {
                    return
                }
            }
            HashMapEntry::Vacant(_) => {
                // This should never happen because the bisection between the two maps
                unreachable!("sender count not found {:?}", sender);
            }
        };
    }
}
