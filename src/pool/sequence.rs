// -----sequence.rs-----

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::Arc;

use tokio::sync::broadcast::{error::TryRecvError, Receiver};
use alloy::primitives::TxHash;
use alloy::consensus::{Transaction, TxEnvelope};

use crate::{
    ordering::TransactionOrdering,
    pool::pending::PendingTransaction,
    identifiers::TransactionId,
};

pub struct TransactionSequence<O>
where
    O: TransactionOrdering,
{
    /// Contains a copy of _all_ transactions of the pending pool at the point in time this
    /// iterator was created.
    pub(crate) all: BTreeMap<TransactionId, PendingTransaction<O>>,
    /// Transactions that can be executed right away: these have the expected nonce.
    ///
    /// Once an `independent` transaction with the nonce `N` is returned, it unlocks `N+1`, which
    /// then can be moved from the `all` set to the `independent` set.
    pub(crate) independent: BTreeSet<PendingTransaction<O>>,
    /// There might be the case where a yielded transactions is invalid, this will track it.
    pub(crate) invalid: HashSet<TxHash>,
}

impl<O: TransactionOrdering> TransactionSequence<O> {
    /// Mark the transaction and it's descendants as invalid.
    pub(crate) fn mark_invalid(&mut self, tx: &Arc<TxEnvelope>) {
        self.invalid.insert(*tx.tx_hash());
    }

    /// Returns the ancestor the given transaction, the transaction with `nonce - 1`.
    ///
    /// Note: for a transaction with nonce higher than the current on chain nonce this will always
    /// return an ancestor since all transaction in this pool are gapless.
    pub(crate) fn ancestor(&self, id: &TransactionId) -> Option<&PendingTransaction<O>> {
        self.all.get(&id.unchecked_ancestor()?)
    }
}

impl<O: TransactionOrdering> Iterator for TransactionSequence<O> {
    type Item = Arc<PendingTransaction<O>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Remove the next independent tx with the highest priority
            let best = self.independent.pop_last()?;
            let hash = best.transaction().tx_hash();

            // skip transactions that were marked as invalid
            if self.invalid.contains(hash) {
                println!(
                    "[{:?}] skipping invalid transaction",
                    hash
                );
                continue
            }

            // Insert transactions that just got unlocked.
            if let Some(unlocked) = self.all.get(&best.unlocks()) {
                self.independent.insert(unlocked.clone());
            }
            return Some(Arc::new(best));
        }
    }
}

/// A[`TransactionSequence`] implementation that filters the
/// transactions of iter with predicate.
///
/// Filter out transactions are marked as invalid:
/// [`TransactionSequence::mark_invalid`]
pub struct TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
{
    pub(crate) transaction_sequence: TransactionSequence<O>,
    pub(crate) predicate: P,
}

impl<O, P> TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
{
    /// Create a new [`TransactionSequenceFilter`] with the given predicate.
    pub(crate) const fn new(transaction_sequence: TransactionSequence<O>, predicate: P) -> Self {
        Self { transaction_sequence, predicate }
    }
}

impl<O, P> Iterator for TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
    P: FnMut(&<TransactionSequence<O> as Iterator>::Item) -> bool,
{
    type Item = <TransactionSequence<O> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let best = self.transaction_sequence.next()?;
            if (self.predicate)(&best) {
                return Some(best)
            }
            self.transaction_sequence.mark_invalid(&best.transaction());
        }
    }
}
