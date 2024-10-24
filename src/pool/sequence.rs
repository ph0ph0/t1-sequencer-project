// -----sequence.rs-----

use std::collections::{BTreeMap, BTreeSet, HashSet};

use tokio::sync::mpsc::Receiver;
use alloy::primitives::TxHash;

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
