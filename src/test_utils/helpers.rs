//! Test utility helpers for transaction and sender creation.
//!
//! This module provides functions to create test senders and transactions
//! for use in testing environments. It includes utilities for generating
//! random Ethereum addresses, signing keys, and creating transaction envelopes.

use std::sync::Arc;

use alloy::{
    consensus::TxEnvelope,
    network::{Ethereum, EthereumWallet, NetworkWallet},
    primitives::{Address, TxKind, U256},
    rpc::types::TransactionRequest,
    signers::{k256::Secp256k1, local::LocalSigner, utils::secret_key_to_address},
};
use ecdsa::SigningKey;
use rand_core::OsRng;

use crate::pool::{
    state::{SubPool, TxState},
    PoolInternalTransaction,
};

// === Sender and Transactions ===

pub fn create_sender() -> (Address, SigningKey<Secp256k1>) {
    let private_key = SigningKey::random(&mut OsRng);
    let address = secret_key_to_address(&private_key);
    (address, private_key)
}
pub async fn create_tx(
    private_key: SigningKey<Secp256k1>,
    sender: Address,
    max_fee_per_gas: u128,
    max_priority_fee_per_gas: u128,
    gas_limit: u64,
    value: U256,
    nonce: u64,
) -> Arc<TxEnvelope> {
    // Create the transaction request first
    let req = TransactionRequest {
        from: None,
        to: Some(TxKind::Call(Address::random())),
        gas_price: None,
        max_fee_per_gas: Some(max_fee_per_gas),
        max_priority_fee_per_gas: Some(max_priority_fee_per_gas),
        max_fee_per_blob_gas: None,
        gas: Some(gas_limit),
        value: Some(value),
        input: Default::default(),
        nonce: Some(nonce),
        chain_id: Some(1),
        access_list: None,
        transaction_type: None,
        blob_versioned_hashes: None,
        sidecar: None,
        authorization_list: None,
    };
    // Build the typed transaction
    let typed_tx = req.build_typed_tx().expect("Failed to build typed tx");
    // Create the local signer
    let local_signer: LocalSigner<SigningKey<Secp256k1>> =
        LocalSigner::from_signing_key(private_key);
    // Create the wallet
    let wallet = EthereumWallet::new(local_signer);
    // Sign the transaction
    let tx_env = <EthereumWallet as NetworkWallet<Ethereum>>::sign_transaction_from(
        &wallet, sender, typed_tx,
    )
    .await
    .unwrap();

    assert!(tx_env.is_eip1559(), "Transaction is not EIP1559");
    // Return the transaction envelope
    Arc::new(tx_env)
}

pub async fn create_tx_and_sender(
    max_fee_per_gas: u128,
    max_priority_fee_per_gas: u128,
    gas_limit: u64,
    value: U256,
    nonce: u64,
) -> (Arc<TxEnvelope>, Address, SigningKey<Secp256k1>) {
    let (sender, private_key) = create_sender();
    let tx = create_tx(
        private_key.clone(),
        sender,
        max_fee_per_gas,
        max_priority_fee_per_gas,
        gas_limit,
        value,
        nonce,
    )
    .await;

    (tx, sender, private_key)
}

pub async fn create_default_tx_and_sender() -> (Arc<TxEnvelope>, Address, SigningKey<Secp256k1>) {
    create_tx_and_sender(10, 20, 100000, U256::ZERO, 0).await
}

pub async fn create_default_tx_envelope_and_sender() -> (TxEnvelope, Address, SigningKey<Secp256k1>)
{
    let (tx, sender, private_key) = create_default_tx_and_sender().await;
    let tx_envelope = Arc::try_unwrap(tx).expect("Failed to unwrap Arc<TxEnvelope>");
    (tx_envelope, sender, private_key)
}

pub async fn create_tx_envelope_with_sender(
    private_key: SigningKey<Secp256k1>,
    sender: Address,
    max_fee_per_gas: u128,
    max_priority_fee_per_gas: u128,
    gas_limit: u64,
    value: U256,
    nonce: u64,
) -> TxEnvelope {
    let tx = create_tx(
        private_key,
        sender,
        max_fee_per_gas,
        max_priority_fee_per_gas,
        gas_limit,
        value,
        nonce,
    )
    .await;

    Arc::try_unwrap(tx).expect("Failed to unwrap Arc<TxEnvelope>")
}

// === Pool Internal Transaction ===

pub fn create_pool_internal_tx(tx: Arc<TxEnvelope>) -> PoolInternalTransaction {
    let mut state = TxState::default();
    state.insert(TxState::NO_PARKED_ANCESTORS);
    state.insert(TxState::NO_NONCE_GAPS);
    state.insert(TxState::ENOUGH_BALANCE);
    state.insert(TxState::NOT_TOO_MUCH_GAS);
    state.insert(TxState::ENOUGH_FEE_CAP_BLOCK);
    state.insert(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);

    assert!(state.is_pending());

    let subpool = SubPool::from(state);

    assert_eq!(subpool, SubPool::Pending);

    let pool_internal_tx = PoolInternalTransaction {
        transaction: Arc::clone(&tx),
        subpool: subpool,
        state: state,
        cumulative_cost: U256::ZERO,
    };

    pool_internal_tx
}

pub fn create_pool_internal_tx_with_cumulative_cost(
    tx: Arc<TxEnvelope>,
    cumulative_cost: U256,
) -> PoolInternalTransaction {
    let mut state = TxState::default();
    state.insert(TxState::NO_PARKED_ANCESTORS);
    state.insert(TxState::NO_NONCE_GAPS);
    state.insert(TxState::ENOUGH_BALANCE);
    state.insert(TxState::NOT_TOO_MUCH_GAS);
    state.insert(TxState::ENOUGH_FEE_CAP_BLOCK);
    state.insert(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);

    assert!(state.is_pending());

    let subpool = SubPool::from(state);

    assert_eq!(subpool, SubPool::Pending);

    let pool_internal_tx = PoolInternalTransaction {
        transaction: Arc::clone(&tx),
        subpool,
        state,
        cumulative_cost,
    };

    pool_internal_tx
}
