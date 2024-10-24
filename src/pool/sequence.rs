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
    /// Used to receive any new pending transactions that have been added to the pool after this
    /// iterator was static fileted
    ///
    /// These new pending transactions are inserted into this iterator's pool before yielding the
    /// next value
    pub(crate) new_transaction_receiver: Option<Receiver<PendingTransaction<O>>>,
}

impl<T: TransactionOrdering> TransactionSequence<T> {
    /// Mark the transaction and it's descendants as invalid.
    pub(crate) fn mark_invalid(&mut self, tx: &Arc<TxEnvelope>) {
        self.invalid.insert(*tx.tx_hash());
    }

    /// Returns the ancestor the given transaction, the transaction with `nonce - 1`.
    ///
    /// Note: for a transaction with nonce higher than the current on chain nonce this will always
    /// return an ancestor since all transaction in this pool are gapless.
    pub(crate) fn ancestor(&self, id: &TransactionId) -> Option<&PendingTransaction<T>> {
        self.all.get(&id.unchecked_ancestor()?)
    }

    /// Non-blocking read on the new pending transactions subscription channel
    fn try_recv(&mut self) -> Option<PendingTransaction<T>> {
        loop {
            match self.new_transaction_receiver.as_mut()?.try_recv() {
                Ok(tx) => return Some(tx),
                // note TryRecvError::Lagged can be returned here, which is an error that attempts
                // to correct itself on consecutive try_recv() attempts

                // the cost of ignoring this error is allowing old transactions to get
                // overwritten after the chan buffer size is met
                Err(TryRecvError::Lagged(_)) => {
                    // Handle the case where the receiver lagged too far behind.
                    // `num_skipped` indicates the number of messages that were skipped.
                    continue
                }

                // this case is still better than the existing iterator behavior where no new
                // pending txs are surfaced to consumers
                Err(_) => return None,
            }
        }
    }

    /// Checks for new transactions that have come into the `PendingPool` after this iterator was
    /// created and inserts them
    fn add_new_transactions(&mut self) {
        while let Some(pending_tx) = self.try_recv() {
            let sender = pending_tx.sender();
            let nonce = pending_tx.transaction().nonce();
            let tx_id = TransactionId::new(sender, nonce);
            if self.ancestor(&tx_id).is_none() {
                self.independent.insert(pending_tx.clone());
            }
            self.all.insert(tx_id, pending_tx);
        }
    }
}