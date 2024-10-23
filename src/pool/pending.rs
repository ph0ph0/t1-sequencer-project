
// -----pending.rs-----

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use alloy::{
    consensus::{TxEnvelope, Transaction},
    primitives::Address,
};

use crate::{
    identifiers::TransactionId,
    ordering::{Priority, TransactionOrdering},
};

#[derive(Eq, PartialEq)]
pub struct PendingTransaction<O>
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    submission_id: u64,
    transaction: Arc<TxEnvelope>,
    priority: Priority<O::PriorityValue>,
    // alloy Transaction type doesn't contain a sender field, so we must extract it from the TxEnvelope
    sender: Address
}

impl<O> Ord for PendingTransaction<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    // TODO: Probs need to remove the nonce sort as it is not needed
    fn cmp(&self, other: &Self) -> Ordering {
        // Primary sort by priority fee (descending)
        other.priority.cmp(&self.priority)
            // Secondary sort by address
            .then(self.sender.cmp(&other.sender))
    }
}

impl<O> PartialOrd for PendingTransaction<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<O: TransactionOrdering> Clone for PendingTransaction<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    fn clone(&self) -> Self {
        Self {
            submission_id: self.submission_id,
            transaction: Arc::clone(&self.transaction),
            priority: self.priority.clone(),
            sender: self.sender
        }
    }
}


// TODO: Add derive
pub struct PendingPool<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
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
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    /// Retrieves a transaction with the given ID from the pool, if it exists.
    fn get(&self, id: &TransactionId) -> Option<&PendingTransaction<O>> {
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

    /// Adds a new transactions to the pending queue.
    ///
    /// # Panics
    ///
    /// if the transaction is already included
    pub fn add_transaction(
        &mut self,
        tx: Arc<TxEnvelope>,
        base_fee: u64,
    ) {
        let sender = tx.recover_signer().unwrap();
        let tx_id = TransactionId::new(sender, tx.nonce());

        assert!(
            !self.contains(&tx_id),
            "transaction already included {:?}",
            self.get(&tx_id).unwrap().transaction
        );

        let submission_id = self.next_id();
        let priority = self.ordering.priority(&tx, base_fee);
        let tx = PendingTransaction { submission_id, transaction: tx, priority, sender };

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
    pub(crate) fn remove_transaction(
        &mut self,
        id: &TransactionId,
    ) -> Option<Arc<TxEnvelope>> {
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
}