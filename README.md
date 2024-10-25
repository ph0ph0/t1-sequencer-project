# t1-protocol Transaction Sequencer

## Overview

This project implements a transaction pool/sequencer for t1 protocol. Currently, it only sequences Eip1559 transactions. However, it has been designed to be extensible to other transaction types in the future, as it uses [Alloy's](https://docs.rs/alloy/0.5.2/alloy/consensus/enum.TxEnvelope.html) `TxEnvelope` type.

The `Pool` type is the main component of the system. It manages the lifecycle and organization of transactions.

The `TransactionSequence` type is a helper type that provides an iterator over the optimal set of transactions ready for execution, considering their priority fees and maintaining proper nonce ordering for each sender.

### Key Features

- **Flexible Transaction Ordering**: Implements customizable transaction ordering strategies, with a default focus on maximizing miner revenue through a priority fee ordering system.
- **Nonce-based Sequencing**: Ensures transactions from the same sender are processed in the correct order based on their nonces, irrespective of the transaction ordering strategy.
- **Filterable Transaction Sequence**: The transaction sequence can be filtered according to arbitrary predicates. (eg sender address, minimum priority fee, etc).
- **DDoS Protection**: The pool is designed to provide some protection against DDoS attacks by limiting the number of transactions from any single sender. The limit is configurable.
- **Pending and Queued Pools**: Separates transactions into pending (ready for inclusion) and queued (waiting for prerequisites) pools for better organization and processing.
- **Dynamic Pool Management**: Automatically moves transactions between pending and queued states based on their readiness for inclusion.
- **Flexible Configuration**: Allows for easy adjustment of pool behavior through the `PoolConfig` settings.
- **Transaction Validation**: Includes basic validation checks to ensure only valid transactions enter the pool.
- **Configurable Limits**: Allows setting of various limits such as maximum account slots and block gas limit to prevent spam and ensure efficient resource usage.
- **Dynamic Fee Handling**: Supports EIP-1559 style dynamic fee transactions, considering base fee and priority fee for transaction ordering.
- **Concurrency Support**: Designed with thread-safety in mind, allowing for concurrent access and modifications.
- **Testing**: The project includes a test suite to ensure reliability and correctness.

## Pool Type

The `Pool` struct, defined in `pool/mod.rs`, serves as the central component of the transaction sequencing system. It orchestrates the lifecycle and organization of transactions within the pool.

New transactions are introduced to the pool through the `add_transaction` method. This method performs necessary validations before assigning the transaction to the appropriate subpool.

To facilitate transaction execution, the `Pool` struct offers a `transaction_sequence` method. This method returns an iterator that yields the most optimal set of transactions. These transactions are ordered based on their priority fees (or any other transaction ordering strategy) while maintaining the correct nonce sequence for each sender. The returned transactions are guaranteed to be executable against the current **chain** state, ensuring no nonce gaps and sufficient on-chain balance.

### Structure

The `Pool` struct is generic over a transaction ordering type, which must implement the `TransactionOrdering` trait. This allows for flexible and customizable transaction prioritization strategies. The main components of the `Pool` struct are:

- `config`: Holds the configuration parameters for the pool.
- `all_transactions`: A collection of all validated transactions in the pool, regardless of their state.
- `pending_transactions`: Manages transactions that are ready for inclusion in a block.
- `queued_transactions`: Holds transactions that are waiting for their prerequisites to be met.

### Functionality

The `Pool` type provides methods for managing transactions:

1. **Adding Transactions**: 
   - `add_transaction`: Adds a new transaction to the pool, performing necessary validations and determining its appropriate subpool. Moves/replaces transactions in pools where necessary.

2. **Retrieving Transactions**:
   - `transaction_sequence`: Provides an iterator over the optimal set of transactions ready for execution, considering their priority fees and maintaining proper nonce ordering for each sender.

## Usage

```rust
use alloy::{
    consensus::TxEnvelope,
    network::{Ethereum, EthereumWallet, NetworkWallet},
    primitives::{Address, U256, TxKind},
    rpc::types::TransactionRequest,
    signers::{
         k256::Secp256k1,
         local::LocalSigner,
         utils::secret_key_to_address,
     },
 };
 use ecdsa::SigningKey;
 use rand_core::OsRng;
 
 use t1_sequencer_project::{Pool, PoolConfig, CoinbaseTipOrdering};
 
#[tokio::main]
async fn main() {
    // Create the pool config
    let config = PoolConfig {
        max_account_slots: 16,
        block_gas_limit: 30_000_000,
        minimal_protocol_basefee: 1,
        pending_base_fee: 1,
    };
    
    // Create the ordering strategy
    let ordering: CoinbaseTipOrdering<TxEnvelope> = CoinbaseTipOrdering::default();

    // Create the pool
    let mut pool = Pool::new(config, ordering);

    // Create the sender
    let private_key = SigningKey::random(&mut OsRng);
    let sender = secret_key_to_address(&private_key);

    // Create the transaction request
    let req = TransactionRequest {
        from: None,
        to: Some(TxKind::Call(Address::random())),
        max_fee_per_gas: Some(20),
        max_priority_fee_per_gas: Some(10),
        gas: Some(100_000),
        value: Some(U256::from(1)),
        nonce: Some(0),
        chain_id: Some(1),
        ..Default::default()
    };

    // Build the typed transaction
    let typed_tx = req.build_typed_tx().expect("Failed to build typed tx");

    // Create the local signer
    let local_signer: LocalSigner<SigningKey<Secp256k1>> = LocalSigner::from_signing_key(private_key);
    let wallet = EthereumWallet::new(local_signer);

    // Sign the transaction
    let tx_env = <EthereumWallet as NetworkWallet<Ethereum>>::sign_transaction_from(&wallet, sender, typed_tx).await.unwrap();

    // Create the on-chain balance and nonce
    let on_chain_balance = U256::from(1_000_000_000);
    let on_chain_nonce = 0;

    // Add the transaction to the pool
    let result = pool.add_transaction(tx_env, on_chain_balance, on_chain_nonce);

    // Get the transaction sequence
    let mut sequence = pool.transaction_sequence();
    let tx = sequence.next().unwrap();
}
```


## Configuration

The pool can be configured with the following parameters:

- `max_account_slots`: Maximum number of transactions allowed per account.
- `block_gas_limit`: Maximum gas limit for a block, used for transaction selection.
- `minimal_protocol_basefee`: Minimum base fee allowed by the protocol.
- `pending_base_fee`: Current base fee used for transaction priority calculations.

## Development Roadmap

- **Additional Transaction Types**:
  - Add support for partially encrypted user intents.
  - Alternatively, add support for more transaction types, such as Eip2930 and Eip4844 transactions.
- **Enhanced Mempool Management**:
   - Implement more sophisticated eviction policies for when the pool reaches capacity.
   - Add extra support for transaction replacement.
- **Transaction Simulation**:
  - Implement transaction simulation functionality to allow for more effective/accurate transaction prioritization.
- **Pool Metrics**:
  - Add pool metrics data structures and monitoring functionality.
- **New Transaction Notification System**:
  - Implement a notification system to update the transaction sequence when new transactions are added.
- **Fine Tuned DDoS Protection**:
  - Add a total transaction limit to the pool to provide a hard limit on the number of transactions that can be added to the pool.
  - Implement transaction limits on a per-pool basis to give greater control over pool behavior.
- **Network Layer Integration**:
   - Add a P2P protocol for efficient transaction propagation.
- **Regulatory Compliance**:
   - Develop features to assist with regulatory compliance, such as transaction origin tracking or blacklist filtering.
- **Cross-chain Compatibility**:
   - Extend the pool to support multiple chain types, allowing for use in cross-chain applications.
- **Debugging and Testing**:
  - Add additional tests and debugging functionality to aid in the development and testing of the pool.
