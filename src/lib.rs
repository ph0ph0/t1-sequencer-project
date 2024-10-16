// -----sequence.rs-----

// pub struct TransactionSequence<T: TransactionOrdering> {

// }

// -----ordering.rs-----

use std::{fmt, marker::PhantomData};
use alloy::{
    consensus::Transaction,
    primitives::U256
};

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

impl<T: Ord + Clone> From<Option<T>> for Priority<T> {
    fn from(value: Option<T>) -> Priority<T> {
        value.map_or(Self::None, Priority::Value)
    }
}

pub struct CoinbaseTipOrdering<T>(PhantomData<T>);

impl<T> TransactionOrdering<T> for CoinbaseTipOrdering<T> 
where   
    T: Transaction + 'static,
{
    
    type PriorityValue = U256;

    fn priority(
        &self,
        transaction: &T,
        base_fee: u64,
    ) -> Priority<Self::PriorityValue> {
        transaction.effective_tip_per_gas(base_fee).map(U256::from).into()
    }
}

impl<T> Default for CoinbaseTipOrdering<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> Clone for CoinbaseTipOrdering<T> {
    fn clone(&self) -> Self {
        Self::default()
    }
}