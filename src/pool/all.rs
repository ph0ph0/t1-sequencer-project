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

#[derive(Debug, Clone, Default)]
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
    pub(crate) fn new(&self) -> Self {
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
}


#[cfg(test)]
mod tests {
    use super::*;
    
    use alloy::primitives::{B256, U256};

    use crate::test_utils::helpers::{
        create_default_tx_and_sender, 
        create_pool_internal_tx,
        create_tx,
    };

    #[tokio::test]
    async fn test_tx_inc_and_decr() {
        let mut all_txs = AllTransactions::default();
        let sender = Address::random();
        let (tx, _, _) = create_default_tx_and_sender().await;
        let tx_id = TransactionId::from(Arc::clone(&tx));
        let pool_internal_tx = create_pool_internal_tx(Arc::clone(&tx));
        all_txs.txs.insert(tx_id, pool_internal_tx);

        all_txs.tx_inc(sender);
        assert_eq!(all_txs.tx_counter.get(&sender).unwrap().clone(), 1usize);

        all_txs.tx_inc(sender);
        assert_eq!(all_txs.tx_counter.get(&sender).unwrap().clone(), 2usize);

        all_txs.tx_decr(sender);
        assert_eq!(all_txs.tx_counter.get(&sender).unwrap().clone(), 1usize);

        all_txs.tx_decr(sender);
        assert!(all_txs.tx_counter.get(&sender).is_none());

        // Decrementing when count is already 0 should have no effect
        all_txs.tx_decr(sender);
        assert!(all_txs.tx_counter.get(&sender).is_none());
    }

    #[tokio::test]
    async fn test_remove_transaction_by_hash() {
        let mut all_txs = AllTransactions::default();
        let (tx, sender, _) = create_default_tx_and_sender().await;
        let tx_hash = tx.tx_hash();
        let tx_id = TransactionId::from(Arc::clone(&tx));
        let pool_internal_tx = create_pool_internal_tx(Arc::clone(&tx));

        // Insert the transaction
        all_txs.txs.insert(tx_id.clone(), pool_internal_tx);
        all_txs.by_hash.insert(tx_hash.clone(), Arc::clone(&tx));
        all_txs.tx_inc(sender);

        // Verify initial state
        assert_eq!(all_txs.txs.len(), 1);
        assert_eq!(all_txs.tx_counter.get(&sender).unwrap().clone(), 1usize);

        // Remove the transaction
        let (removed_tx, removed_pool) = all_txs.remove_transaction_by_hash(&tx_hash).unwrap();

        // Verify the removed transaction
        assert_eq!(removed_tx.tx_hash(), tx_hash);
        assert_eq!(removed_pool, SubPool::Pending);

        // Verify final state
        assert!(all_txs.txs.is_empty());
        assert_eq!(all_txs.tx_counter.get(&sender), None);

        // Attempt to remove a non-existent transaction
        assert!(all_txs.remove_transaction_by_hash(&B256::random()).is_none());
    }

    #[tokio::test]
    async fn test_descendant_txs_mut() {
        // Create 3 transactions with the same sender
        let mut all_txs = AllTransactions::default();
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key.clone(), sender, 10, 20, 100000, U256::ZERO, 1).await;
        let tx3 = create_tx(private_key, sender, 10, 20, 100000, U256::ZERO, 2).await;

        // Get the transaction ids
        let tx1_id = TransactionId::from(Arc::clone(&tx1));
        let tx2_id = TransactionId::from(Arc::clone(&tx2));
        let tx3_id = TransactionId::from(Arc::clone(&tx3));

        // Insert the transactions into the pool
        all_txs.txs.insert(tx1_id.clone(), create_pool_internal_tx(Arc::clone(&tx1)));
        all_txs.txs.insert(tx2_id.clone(), create_pool_internal_tx(Arc::clone(&tx2)));
        all_txs.txs.insert(tx3_id.clone(), create_pool_internal_tx(Arc::clone(&tx3)));

        // Get the descendants
        let descendants: Vec<_> = all_txs.descendant_txs_mut(&tx1_id).collect();

        // Verify the descendants
        assert_eq!(descendants.len(), 3);
        assert_eq!(descendants[0].0, &tx1_id);
        assert_eq!(descendants[1].0, &tx2_id);
        assert_eq!(descendants[2].0, &tx3_id);

        // Test with a transaction that has no descendants
        let descendants_of_tx3: Vec<_> = all_txs.descendant_txs_mut(&tx3_id).collect();
        assert_eq!(descendants_of_tx3.len(), 1);
        assert_eq!(descendants_of_tx3[0].0, &tx3_id);

        // Test with a non-existent transaction
        let (tx_two, sender_two, _) = create_default_tx_and_sender().await;
        let tx_two_id = TransactionId::from(Arc::clone(&tx_two));
        let non_existent_descendants: Vec<_> = all_txs.descendant_txs_mut(&tx_two_id).collect();
        assert!(non_existent_descendants.is_empty());
    }
}


