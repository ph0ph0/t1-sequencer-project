// -----sequence.rs-----

use std::collections::BTreeSet
;

use crate::{
    ordering::TransactionOrdering,
    pool::pending::PendingTransaction,
};

pub struct TransactionSequence<O>
where
    O: TransactionOrdering,
{
    ordering: O,
    sequenced_transactions: BTreeSet<PendingTransaction<O>>,
    // nonce_map: HashMap<u64, u64>, //TODO: Remove
    sum_priority_fee: u128,
}

impl<O> TransactionSequence<O>
where
    O: TransactionOrdering,
{
    pub fn new(ordering: O) -> Self {
        Self { ordering, sequenced_transactions: BTreeSet::default(), sum_priority_fee: 0 }
    }
}
