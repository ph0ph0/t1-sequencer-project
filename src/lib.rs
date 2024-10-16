// -----sequence.rs-----

// pub struct TransactionSequence<T: TransactionOrdering> {

// }

// -----ordering.rs-----

use std::fmt;
use alloy::consensus::Transaction;

pub trait TransactionOrdering<T: Transaction>: Send + Sync + 'static {
    
    type PriorityValue: Ord + Clone + Default + fmt::Debug + Send + Sync;

    fn priority(
        &self,
        transaction: &T,
        base_fee: u64,
    ) -> Priority<Self::PriorityValue>;
}

pub enum Priority<T> {
    Value(T),
    None,
}