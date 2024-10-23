
// -----all_transactions.rs----

use std::{
    collections::{BTreeMap, HashMap, hash_map},
    sync::Arc,
};
use alloy::{
    primitives::{Address, TxHash},
    consensus::TxEnvelope,
};
use crate::{
    pool::{PoolInternalTransaction, state::SubPool},
    identifiers::TransactionId,
};

pub struct AllTransactions
where 
{
    /// All transactions in the pool, grouped by sender, orderd by nonce
    pub(crate) txs: BTreeMap<TransactionId, PoolInternalTransaction>,
    /// All transactions in the pool ordered by hash
    pub(crate) by_hash: HashMap<TxHash, Arc<TxEnvelope>>,
    /// Keeps track of the number of transactions by sender currently in the system
    pub(crate) tx_counter: HashMap<Address, usize>,
}

impl AllTransactions
{
    /// Creates new instance
    fn new(&self) -> Self {
        Self {
            txs: BTreeMap::new(),
            by_hash: HashMap::new(),
            tx_counter: HashMap::new()
        }
    }

    pub(crate) fn contains(&self, tx_hash: &TxHash) -> bool {
        self.by_hash.contains_key(tx_hash)
    }

    pub(crate) fn tx_inc(&mut self, sender: Address) {
        let count = self.tx_counter.entry(sender).or_default();
        *count += 1;
    }

    pub(crate) fn tx_decr(&mut self, sender: Address) {
        if let hash_map::Entry::Occupied(mut entry) = self.tx_counter.entry(sender) {
            let count = entry.get_mut();

            if *count == 1 {
                entry.remove();
                return;
            }
            *count -= 1;
        }
    }

    /// Returns all mutable transactions that _follow_ after the given id but have the same sender.
    ///
    /// NOTE: The range is _inclusive_: if the transaction that belongs to `id` it field be the
    /// first value.
    pub(crate) fn descendant_txs_mut<'a, 'b: 'a>(
        &'a mut self,
        id: &'b TransactionId,
    ) -> impl Iterator<Item = (&'a TransactionId, &'a mut PoolInternalTransaction)> + 'a {
        self.txs.range_mut(id..).take_while(|(other, _)| id.sender == other.sender)
    }

    /// Removes a transaction from the set using its hash.
    pub(crate) fn remove_transaction_by_hash(
        &mut self,
        tx_hash: &TxHash,
    ) -> Option<(Arc<TxEnvelope>, SubPool)> {
        let tx = self.by_hash.remove(tx_hash)?;
        let tx_id = TransactionId::from(Arc::clone(&tx));
        let internal = self.txs.remove(&tx_id)?;
        // decrement the counter for the sender.
        self.tx_decr(TransactionId::from(Arc::clone(&tx)).sender);
        Some((tx, internal.subpool))
    }

    // TODO:
    // pub(crate) update(
    //     &mut self,
    //     changed_accounts: HashMap<Address, SenderInfo>
    // ) -> Vec<PoolUpdate> {

    // }
}