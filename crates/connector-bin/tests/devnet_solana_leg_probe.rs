//! Devnet acceptance probe for the SOLANA settlement leg: a real, funded
//! `packages/solana-program` payment channel, an Ed25519 balance proof signed
//! over it, and a paid write bought from a live node's client edge with that
//! proof carried in the `ilp-payment-channel-claim` header.
//!
//! This is the Solana twin of `devnet_store_leg_probe.rs`, whose `claim_json`
//! builds only the EVM/EIP-712 form. A node can advertise `[settlement.solana]`
//! -- announce it, greet with it, fund it -- without a single claim ever having
//! crossed that leg, because until this file existed no client could produce
//! one. "Advertises Solana" and "has settled on Solana" are different claims
//! and only the second is evidence.
//!
//! ## What a green run proves, in order
//!
//!   1. the channel named on the command line is genuinely open on the
//!      deployed program, in the mint the node settles in, with the payer as a
//!      participant and a real on-chain deposit behind them;
//!   2. the node resolves that channel FROM CHAIN -- nothing about it is in
//!      the node's config -- and will say what it has already accepted on it;
//!   3. a PAID, sealed, Ed25519-claim-bearing packet FULFILLs, and the app
//!      behind the route answers;
//!   4. the node's own claim-state reading advances by the route's price,
//!      which is the number a soak is counted in.
//!
//! ## LOCAL / DEV ONLY, and inert unless driven
//!
//! Every test returns immediately unless `SOLANA_PROBE_EDGE` is set -- the same
//! gate `devnet_store_leg_probe.rs` uses, so an ordinary `cargo test` run never
//! needs a live node. The paid test SPENDS REAL DEVNET VALUE and ADVANCES THE
//! CHANNEL WATERMARK.
//!
//!   # read-only: what the chain and the node each say about the channel
//!   SOLANA_PROBE_EDGE=https://connector.167-233-221-236.sslip.io \
//!   SOLANA_PROBE_PAYER_KEYPAIR=~/.config/solana/id.json \
//!   SOLANA_PROBE_NODE=4s2JSwCFJZ7iTmPoLXLhFnfrEvybMTxuWCA2LfMRhyv1 \
//!     cargo test -p connector --test devnet_solana_leg_probe -- --nocapture \
//!       the_channel
//!
//!   # one-time: open the channel and deposit into it (SPENDS SOL AND TOKENS)
//!   SOLANA_PROBE_OPEN=1 SOLANA_PROBE_DEPOSIT=2000000 ...same... \
//!     cargo test -p connector --test devnet_solana_leg_probe -- --nocapture \
//!       open_and_fund
//!
//!   # the paid round trip
//!   ...same... cargo test -p connector --test devnet_solana_leg_probe \
//!     -- --nocapture a_paid_solana_claim
//!
//! ## The traps this file exists to keep written down
//!
//!   * **The claim's `signature` is BASE64, not hex.** Every other signature
//!     on this wire is `0x`-hex, and the EVM claim next door is. The Solana
//!     branch of the claim gate decodes `signature` with the STANDARD base64
//!     engine (`claim_gate.rs`'s `verify_solana_claim_signature`), so a hex
//!     signature is not a wrong signature -- it fails to decode at all and
//!     comes back as the same `SignatureInvalid` a forgery would.
//!
//!   * **The signed bytes are 48 raw bytes, not a digest and not a JSON
//!     string:** `channel_account || nonce (LE) || transferred_amount (LE)`,
//!     which is `connector_signer::solana_balance_proof_message` and is called
//!     here rather than re-spelled. It is the same message the deployed
//!     program's own Ed25519 precompile check verifies on redemption
//!     (`packages/solana-program/src/processor.rs`, mirrored client-side in
//!     `connector_settlement_solana::wire::balance_proof_message`), so a claim
//!     this node accepts is a claim it can actually redeem.
//!
//!   * **`transferredAmount` is a decimal STRING and `nonce` is a JSON
//!     NUMBER.** `parse_solana` requires exactly that pairing; a numeric
//!     `transferredAmount` is refused as malformed before anything is charged.
//!
//!   * **The channel PDA is derived from SORTED participants.** `["channel",
//!     min(a,b), max(a,b), token_mint]` -- so the payer cannot compute "its"
//!     channel by putting itself first, and the on-chain `participant_a` is
//!     whichever pubkey sorts lower, not whoever opened it. Deposits credit by
//!     signer, so this is invisible until you try to read `deposit_a` and find
//!     your money in `deposit_b`.
//!
//!   * **The node must be a participant, in ITS mint.** `resolvable_counterparty`
//!     refuses a channel whose `token_mint` is not the one `[settlement.solana]`
//!     names, and refuses a settled channel, and refuses one the node is not in
//!     -- each as an indistinguishable "unknown channel". A channel opened
//!     against the right node in the wrong mint looks exactly like a channel
//!     that was never opened.
//!
//!   * **The watermark is the NODE's, not the chain's.** The on-chain
//!     `nonce_a`/`nonce_b` only move on redemption; what refuses a replay is
//!     the node's own journal under `state_dir`, which survives restarts. So
//!     the next usable nonce cannot be read off the chain. This probe reads it
//!     from the node's `/ilp/claim-state` instead -- an Ed25519-challenged
//!     endpoint only the channel's counterparty can answer -- which is what
//!     lets it be run repeatedly without a human bumping a counter, and what
//!     makes it usable as a soak client rather than a one-shot demo.

use std::time::{Duration as StdDuration, SystemTime, UNIX_EPOCH};

use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use chrono::{Duration as ChronoDuration, SecondsFormat, Utc};
use connector_domain::{
    derive_condition, EnvelopeRequest, EnvelopeResponse, Fulfill, Prepare, Reject,
};
use connector_settlement_solana::wire;
use connector_signer::giftwrap::{derive_fulfillment, open_response, seal_request};
use connector_signer::{
    solana_balance_proof_message, solana_claim_state_challenge_message, PublicKeyBytes,
};
use solana_rpc_client::nonblocking::rpc_client::RpcClient;
use solana_sdk::commitment_config::CommitmentConfig;
use solana_sdk::instruction::Instruction;
use solana_sdk::pubkey::Pubkey;
use solana_sdk::signature::{Keypair, Signer as SolanaSigner};
use solana_sdk::transaction::Transaction;

const CLAIM_HEADER: &str = "ilp-payment-channel-claim";

/// The live public-devnet deployment of `packages/solana-program` -- the same
/// id `infra`'s own devnet configs and Drew's node both name. Overridable
/// because nothing here should be pinned to one deployment.
const DEFAULT_PROGRAM_ID: &str = "2aEVJ8koKD8LTZrLRSGtAtU7LBt4e7QjjCgf1kzQ7Rip";
const DEFAULT_RPC_URL: &str = "https://api.devnet.solana.com";

// ── environment ──────────────────────────────────────────────────────────────

fn env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

/// The gate. `None` means every test in this file returns green without doing
/// anything, which is what keeps `cargo test --workspace` free and offline.
fn edge() -> Option<String> {
    env("SOLANA_PROBE_EDGE").map(|value| value.trim_end_matches('/').to_string())
}

fn destination() -> String {
    env("SOLANA_PROBE_DESTINATION").unwrap_or_else(|| "g.drew.relay".to_string())
}

/// `""` would resolve to the handler URL's own base rather than its path --
/// see `devnet_store_leg_probe.rs`'s note. The relay's paid-write endpoint is
/// `/write` beneath `http://relay:3100`.
fn target() -> String {
    env("SOLANA_PROBE_TARGET").unwrap_or_else(|| "/write".to_string())
}

fn rpc() -> RpcClient {
    RpcClient::new_with_commitment(
        env("SOLANA_PROBE_RPC").unwrap_or_else(|| DEFAULT_RPC_URL.to_string()),
        CommitmentConfig::confirmed(),
    )
}

fn program_id() -> Pubkey {
    env("SOLANA_PROBE_PROGRAM")
        .unwrap_or_else(|| DEFAULT_PROGRAM_ID.to_string())
        .parse()
        .expect("SOLANA_PROBE_PROGRAM is a base58 program id")
}

/// The node's own Solana settlement identity -- the other participant of the
/// channel. Deliberately required rather than defaulted: paying the wrong node
/// is not a mistake a default should make easy.
fn node_pubkey() -> Option<Pubkey> {
    Some(
        env("SOLANA_PROBE_NODE")?
            .parse()
            .expect("SOLANA_PROBE_NODE is a base58 pubkey"),
    )
}

/// The payer's keypair, from a Solana CLI keypair file (a JSON array of the 64
/// secret||public bytes) or from 64 bytes of hex. No key is ever committed and
/// none is generated here: a probe that minted its own key would be paying
/// from a wallet nothing funded.
fn payer() -> Option<Keypair> {
    if let Some(path) = env("SOLANA_PROBE_PAYER_KEYPAIR") {
        let expanded = match path.strip_prefix("~/") {
            Some(rest) => format!("{}/{rest}", std::env::var("HOME").expect("HOME")),
            None => path,
        };
        let text = std::fs::read_to_string(&expanded)
            .unwrap_or_else(|error| panic!("read {expanded}: {error}"));
        let bytes: Vec<u8> = serde_json::from_str(&text).expect("a Solana CLI keypair JSON array");
        return Some(Keypair::from_bytes(&bytes).expect("64-byte Solana keypair"));
    }
    let hex = env("SOLANA_PROBE_PAYER_KEY")?;
    let bytes: Vec<u8> = (0..hex.len() / 2)
        .map(|i| u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect();
    Some(Keypair::from_bytes(&bytes).expect("64-byte Solana keypair"))
}

fn hex_decode(s: &str) -> Vec<u8> {
    let s = s.trim_start_matches("0x");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect()
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock")
        .as_secs()
}

// ── the channel, as the chain holds it ───────────────────────────────────────

/// Everything this probe needs about the channel, read from the chain rather
/// than passed in: the mint comes off the account itself, so a run cannot be
/// pointed at the wrong mint and report a missing channel as a broken node.
struct OnChainChannel {
    parsed: wire::ChannelAccount,
}

impl OnChainChannel {
    /// The payer's own side of the two-sided deposit -- the side a claim they
    /// sign redeems against (`processor.rs`'s `Claim` handler bounds against
    /// the claiming participant's own `deposit_x`), and the side the node's
    /// `resolvable_counterparty` reports as this channel's deposit floor.
    fn payer_deposit(&self, payer: &Pubkey) -> u64 {
        if self.parsed.participant_a == *payer {
            self.parsed.deposit_a
        } else {
            self.parsed.deposit_b
        }
    }
}

/// Derive the channel PDA for `payer` and `node` in `mint`, and read it back.
/// `None` means no such account exists -- which is not the same as an error,
/// and the open path below depends on being able to tell those apart.
async fn read_channel(
    client: &RpcClient,
    payer: &Pubkey,
    node: &Pubkey,
    mint: &Pubkey,
) -> (Pubkey, Option<OnChainChannel>) {
    let (account, _bump) = wire::channel_pda(payer, node, mint, &program_id());
    let fetched = client
        .get_account_with_commitment(&account, CommitmentConfig::confirmed())
        .await
        .expect("getAccountInfo")
        .value;
    let parsed = fetched.and_then(|raw| wire::ChannelAccount::parse(&raw.data));
    (account, parsed.map(|parsed| OnChainChannel { parsed }))
}

/// The mint the node settles in. Read from the node's own greeting when it
/// publishes one, else from `SOLANA_PROBE_MINT` -- because the channel PDA
/// depends on it, and guessing it produces an address that simply does not
/// exist rather than an error naming the mismatch.
fn mint() -> Pubkey {
    env("SOLANA_PROBE_MINT")
        .expect("SOLANA_PROBE_MINT: the SPL mint the node's [settlement.solana] names")
        .parse()
        .expect("SOLANA_PROBE_MINT is a base58 mint address")
}

async fn submit(
    client: &RpcClient,
    payer: &Keypair,
    instructions: &[Instruction],
    what: &str,
) -> solana_sdk::signature::Signature {
    let blockhash = client
        .get_latest_blockhash()
        .await
        .expect("latest blockhash");
    let transaction = Transaction::new_signed_with_payer(
        instructions,
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    );
    client
        .send_and_confirm_transaction(&transaction)
        .await
        .unwrap_or_else(|error| panic!("{what} failed on chain: {error}"))
}

// ── the node's own view of the channel ───────────────────────────────────────

/// What the node has already accepted on this channel, from `/ilp/claim-state`
/// (issue #693) -- the endpoint that answers only to an Ed25519 challenge
/// signed by the channel's registered counterparty, so this reading is one
/// only the payer can obtain and cannot be faked into.
///
/// This is the piece that makes the probe re-runnable. The next usable nonce
/// is NOT on chain (on-chain nonces move only on redemption) and NOT derivable
/// from anything local; the node's journal is the authority, and this asks it.
struct NodeClaimState {
    nonce: u64,
    cumulative: u128,
    deposit_total: Option<u128>,
}

async fn fetch_claim_state(
    edge: &str,
    channel_account: &Pubkey,
    payer: &Keypair,
) -> Option<NodeClaimState> {
    let expires = now_secs() + 300;
    let message = solana_claim_state_challenge_message(&channel_account.to_bytes(), expires);
    let signature = payer.sign_message(&message);

    let request = serde_json::json!({
        "channels": [{
            "blockchain": "solana",
            "channelAccount": channel_account.to_string(),
            "expires": expires,
            "signature": BASE64.encode(signature.as_ref()),
        }]
    });
    let body: serde_json::Value = reqwest::Client::new()
        .post(format!("{edge}/ilp/claim-state"))
        .json(&request)
        .send()
        .await
        .expect("POST /ilp/claim-state")
        .json()
        .await
        .expect("claim-state json");

    let entry = &body["channels"][0];
    if entry["ok"] != serde_json::Value::Bool(true) {
        println!(
            "claim-state did not verify this channel: {}",
            serde_json::to_string(entry).expect("json")
        );
        return None;
    }
    Some(NodeClaimState {
        nonce: entry["nonce"].as_u64().expect("nonce"),
        cumulative: entry["cumulativeClaimed"]
            .as_str()
            .expect("cumulativeClaimed is a decimal string")
            .parse()
            .expect("cumulativeClaimed"),
        deposit_total: entry["depositTotal"]
            .as_str()
            .map(|value| value.parse().expect("depositTotal")),
    })
}

// ── the claim ────────────────────────────────────────────────────────────────

/// A genuinely Ed25519-signed Solana client-edge claim
/// (`connector_domain::client_claim::SolanaClientClaim`).
///
/// The signature covers `connector_signer::solana_balance_proof_message` --
/// called, not re-spelled, so this probe cannot drift from the code that
/// verifies it -- and is carried BASE64, which is the one thing about this
/// wire that differs from every other signature the connector handles.
fn solana_claim_json(
    channel_account: &Pubkey,
    payer: &Keypair,
    nonce: u64,
    cumulative: u128,
) -> String {
    let amount = u64::try_from(cumulative).expect("a Solana claim's amount is a u64");
    let message = solana_balance_proof_message(&channel_account.to_bytes(), nonce, amount);
    let signature = payer.sign_message(&message);

    format!(
        r#"{{
            "version": "1.0",
            "blockchain": "solana",
            "messageId": "solana-probe-{nonce}",
            "timestamp": "{timestamp}",
            "senderId": "{signer}",
            "programId": "{program}",
            "channelAccount": "{channel}",
            "nonce": {nonce},
            "transferredAmount": "{amount}",
            "signature": "{signature}",
            "signerPublicKey": "{signer}",
            "cluster": "devnet"
        }}"#,
        // `Z`, not `+00:00` -- the claim gate refuses the offset spelling by
        // name, and `chrono`'s plain `to_rfc3339()` emits exactly that.
        timestamp = Utc::now().to_rfc3339_opts(SecondsFormat::Millis, true),
        signer = payer.pubkey(),
        program = program_id(),
        channel = channel_account,
        signature = BASE64.encode(signature.as_ref()),
    )
}

// ── the packet ───────────────────────────────────────────────────────────────

async fn fetch_identity(base: &str) -> PublicKeyBytes {
    let body: serde_json::Value = reqwest::get(format!("{base}/ilp/identity"))
        .await
        .expect("GET /ilp/identity")
        .json()
        .await
        .expect("identity json");
    let bytes = hex_decode(body["publicKey"].as_str().expect("publicKey"));
    bytes.as_slice().try_into().expect("65-byte public key")
}

async fn fetch_price(base: &str, destination: &str) -> u64 {
    let body: serde_json::Value =
        reqwest::get(format!("{base}/ilp/routes/price?destination={destination}"))
            .await
            .expect("GET /ilp/routes/price")
            .json()
            .await
            .expect("price json");
    body["price"]
        .as_u64()
        .unwrap_or_else(|| panic!("no price for {destination}: {body}"))
}

/// The `Prepare` a real sender forms: an OER `EnvelopeRequest` gift-wrapped to
/// the TERMINATING connector's identity (ADR 0018), under a condition minted
/// from the fulfilment that wrap's shared secret derives (ADR 0019).
fn sealed_prepare(
    amount: u64,
    destination: &str,
    target: &str,
    body: &[u8],
    identity: &PublicKeyBytes,
) -> (Prepare, [u8; 32]) {
    let plaintext = EnvelopeRequest {
        method: "POST".to_string(),
        target: target.to_string(),
        headers: vec![("content-type".to_string(), "application/json".to_string())],
        body: body.to_vec(),
    }
    .encode();
    let (data, shared_secret) = seal_request(&plaintext, identity).expect("seal");
    (
        Prepare {
            amount,
            expires_at: Utc::now() + ChronoDuration::minutes(2),
            execution_condition: derive_condition(&derive_fulfillment(&shared_secret)),
            destination: destination.to_string(),
            data,
        },
        shared_secret,
    )
}

/// A genuinely signed NIP-01 event and the relay's `POST /write` body. The
/// relay verifies the Schnorr signature before storing anything
/// (`TOON_DEV_MODE=false`), which is what makes "the relay stored it" a
/// statement about a real event rather than about a blob this probe made up.
fn signed_nostr_event(content: &str) -> (serde_json::Value, String) {
    use k256::schnorr::signature::hazmat::PrehashSigner;
    use k256::schnorr::SigningKey;
    use sha2::{Digest, Sha256};

    const PUBLISHER_KEY: [u8; 32] = [0x2b; 32];

    let signing_key = SigningKey::from_bytes(&PUBLISHER_KEY).expect("nostr signing key");
    let pubkey = hex_encode(&signing_key.verifying_key().to_bytes());
    let created_at = now_secs();

    let serialized = serde_json::json!([0, pubkey, created_at, 1, [], content]).to_string();
    let id = hex_encode(&Sha256::digest(serialized.as_bytes()));
    let signature: k256::schnorr::Signature = signing_key
        .sign_prehash(&hex_decode(&id))
        .expect("schnorr sign the event id");

    let event = serde_json::json!({
        "id": id,
        "pubkey": pubkey,
        "created_at": created_at,
        "kind": 1,
        "tags": [],
        "content": content,
        "sig": hex_encode(&signature.to_bytes()),
    });
    (event, id)
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn write_body(event: &serde_json::Value) -> Vec<u8> {
    serde_json::json!({ "event": event })
        .to_string()
        .into_bytes()
}

// ── 1. what the chain says ───────────────────────────────────────────────────

#[tokio::test]
async fn the_channel_is_open_and_funded_on_chain_in_the_nodes_own_mint() {
    let (Some(_edge), Some(node), Some(payer)) = (edge(), node_pubkey(), payer()) else {
        return;
    };
    let client = rpc();
    let mint = mint();
    let (account, channel) = read_channel(&client, &payer.pubkey(), &node, &mint).await;

    println!("payer          {}", payer.pubkey());
    println!("node           {node}");
    println!("mint           {mint}");
    println!("channel PDA    {account}");

    let Some(channel) = channel else {
        panic!(
            "no channel account at {account} -- run the open_and_fund test first \
             (SOLANA_PROBE_OPEN=1)"
        );
    };

    // Each of these is a way the node reports "unknown channel" rather than
    // anything more specific (`resolvable_counterparty`), so an unpaid probe
    // that skipped them would be debugging the wrong end.
    assert_eq!(
        channel.parsed.token_mint, mint,
        "the channel's mint must be the one the node settles in, or the node \
         refuses it as an unknown channel"
    );
    assert_eq!(
        channel.parsed.status,
        wire::ChannelStatus::Opened,
        "a closed or settled channel cannot be claimed against"
    );
    let participants = [channel.parsed.participant_a, channel.parsed.participant_b];
    assert!(
        participants.contains(&node),
        "the node {node} is not a participant of {account}: {participants:?}"
    );
    assert!(participants.contains(&payer.pubkey()));

    let deposit = channel.payer_deposit(&payer.pubkey());
    println!("payer deposit  {deposit} base units");
    assert!(
        deposit > 0,
        "the payer's own side of the deposit is 0, so every claim would be \
         refused as undercollateralized"
    );
}

// ── 2. one-time setup: open the channel and deposit into it ──────────────────

/// SPENDS SOL AND TOKENS. Gated on `SOLANA_PROBE_OPEN` on top of the usual
/// gate, so it cannot run by accident when the paid probe does.
///
/// The two instructions are deliberately separate transactions: `Deposit`
/// requires the depositing participant to sign for themselves, and a channel
/// that exists with a zero deposit is a recoverable state, whereas a
/// half-applied combined transaction is not.
#[tokio::test]
async fn open_and_fund_a_solana_channel_with_this_node() {
    let (Some(_edge), Some(node), Some(payer)) = (edge(), node_pubkey(), payer()) else {
        return;
    };
    if env("SOLANA_PROBE_OPEN").is_none() {
        return;
    }
    let client = rpc();
    let mint = mint();
    let program = program_id();
    let payer_pubkey = payer.pubkey();

    let (account, existing) = read_channel(&client, &payer_pubkey, &node, &mint).await;
    let (vault, _bump) = wire::vault_pda(&account, &program);

    if existing.is_none() {
        println!("opening channel {account} (vault {vault})");
        let challenge_duration: u64 = env("SOLANA_PROBE_CHALLENGE_SECS")
            .unwrap_or_else(|| "3600".to_string())
            .parse()
            .expect("challenge duration in seconds");
        let signature = submit(
            &client,
            &payer,
            &[Instruction::new_with_bytes(
                program,
                &wire::pack_initialize_channel(challenge_duration),
                wire::Accounts::initialize_channel(
                    &payer_pubkey,
                    &payer_pubkey,
                    &node,
                    &mint,
                    &account,
                    &vault,
                ),
            )],
            "InitializeChannel",
        )
        .await;
        println!("opened: {signature}");
    } else {
        println!("channel {account} already exists -- skipping InitializeChannel");
    }

    let Some(deposit) = env("SOLANA_PROBE_DEPOSIT") else {
        println!("SOLANA_PROBE_DEPOSIT unset -- opened only, nothing deposited");
        return;
    };
    let deposit: u64 = deposit.parse().expect("deposit in base units");
    let payer_token_account =
        spl_associated_token_account::get_associated_token_address(&payer_pubkey, &mint);
    println!("depositing {deposit} from {payer_token_account}");

    let signature = submit(
        &client,
        &payer,
        &[Instruction::new_with_bytes(
            program,
            &wire::pack_deposit(deposit),
            wire::Accounts::deposit(&payer_pubkey, &payer_token_account, &vault, &account),
        )],
        "Deposit",
    )
    .await;
    println!("deposited: {signature}");

    let (_account, channel) = read_channel(&client, &payer_pubkey, &node, &mint).await;
    let channel = channel.expect("the channel must exist after opening it");
    println!(
        "channel now: deposit={} status={:?}",
        channel.payer_deposit(&payer_pubkey),
        channel.parsed.status
    );
}

// ── 3. the node's own reading of the channel ─────────────────────────────────

/// Proves the node resolves this channel FROM CHAIN. Nothing about it is in
/// the node's config: it was opened by a wallet the node has never heard of,
/// and the only reason the node can answer at all is `[settlement.solana]`
/// giving it a program to go and look in (issue #631).
#[tokio::test]
async fn the_node_resolves_this_channel_from_chain_and_reports_its_watermark() {
    let (Some(edge), Some(node), Some(payer)) = (edge(), node_pubkey(), payer()) else {
        return;
    };
    let client = rpc();
    let (account, _channel) = read_channel(&client, &payer.pubkey(), &node, &mint()).await;

    let state = fetch_claim_state(&edge, &account, &payer)
        .await
        .expect("the node must resolve a channel it is a participant of, from chain");

    println!(
        "node's view of {account}: nonce={} cumulativeClaimed={} depositTotal={:?}",
        state.nonce, state.cumulative, state.deposit_total
    );
    assert!(
        state.deposit_total.is_some(),
        "a chain-resolved channel reports a deposit; `null` means the node took \
         it from config instead, which would make this probe prove nothing about \
         chain resolution"
    );
}

// ── 4. the paid write ────────────────────────────────────────────────────────

/// SPENDS REAL DEVNET VALUE and ADVANCES THE NODE'S WATERMARK.
///
/// The nonce and cumulative amount are read from the node itself rather than
/// passed in, so this is safe to run repeatedly -- which is the whole point:
/// a soak is a count of these, not one of them.
#[tokio::test]
async fn a_paid_solana_claim_buys_a_write_and_advances_the_watermark() {
    let (Some(edge), Some(node), Some(payer)) = (edge(), node_pubkey(), payer()) else {
        return;
    };
    let client = rpc();
    let destination = destination();
    let (account, channel) = read_channel(&client, &payer.pubkey(), &node, &mint()).await;
    let channel = channel.expect("open and fund the channel first");
    let deposit = channel.payer_deposit(&payer.pubkey());

    let before = fetch_claim_state(&edge, &account, &payer)
        .await
        .expect("the node must resolve this channel before it can be paid on it");
    let price = fetch_price(&edge, &destination).await;
    println!(
        "channel {account}\n  on-chain deposit {deposit}\n  node watermark   nonce={} cumulative={}\n  route {destination} price {price}",
        before.nonce, before.cumulative
    );

    // Both default to the node's own reading advanced by one packet, which is
    // what makes repeated runs work unattended. The overrides exist for the
    // one case the default cannot express: deliberately re-presenting a nonce
    // the node has already seen, to watch the replay defence refuse it
    // (`SOLANA_PROBE_NONCE=<a used nonce>`). A replay costs nothing -- it is
    // refused at the gate, before the packet is forwarded.
    let cumulative: u128 = match env("SOLANA_PROBE_CUMULATIVE") {
        Some(value) => value.parse().expect("cumulative"),
        None => before.cumulative + u128::from(price),
    };
    let nonce: u64 = match env("SOLANA_PROBE_NONCE") {
        Some(value) => value.parse().expect("nonce"),
        None => before.nonce + 1,
    };
    assert!(
        cumulative <= u128::from(deposit),
        "this claim ({cumulative}) would exceed the on-chain deposit ({deposit}) \
         and be refused as undercollateralized -- deposit more before running again"
    );
    let claim = solana_claim_json(&account, &payer, nonce, cumulative);

    let identity = fetch_identity(&edge).await;
    let content = format!(
        "paid over the Solana settlement leg -- channel {account} nonce {nonce} at {}",
        Utc::now().to_rfc3339_opts(SecondsFormat::Secs, true)
    );
    let (event, event_id) = signed_nostr_event(&content);
    let (prepare, secret) = sealed_prepare(
        price,
        &destination,
        &target(),
        &write_body(&event),
        &identity,
    );

    let response = reqwest::Client::new()
        .post(format!("{edge}/ilp"))
        .header(CLAIM_HEADER, BASE64.encode(claim.as_bytes()))
        .body(prepare.encode())
        .send()
        .await
        .expect("POST /ilp");
    assert_eq!(response.status(), reqwest::StatusCode::OK);
    let body = response.bytes().await.expect("response body");

    // A REJECT decodes here first so a failure names itself, rather than
    // surfacing as an opaque "could not decode a Fulfill".
    if let Ok(reject) = Reject::decode(&body) {
        panic!(
            "REJECTED {:?} {}: {}",
            reject.code, reject.triggered_by, reject.message
        );
    }
    let fulfill = Fulfill::decode(&body).expect("a Fulfill");
    // The fulfilment is derivable only from the shared secret this sender
    // minted the condition under (ADR 0019) -- the app holds no secret and
    // performs no cryptography, so only the node this packet was sealed to
    // can have produced it.
    assert_eq!(fulfill.fulfillment, derive_fulfillment(&secret));
    let opened = open_response(&secret, &fulfill.data).expect("open the sealed answer");
    let envelope = EnvelopeResponse::decode(&opened).expect("decode envelope");

    println!(
        "FULFILL -- app status {} body {}",
        envelope.status,
        String::from_utf8_lossy(&envelope.body)
    );
    assert!(
        (200..300).contains(&envelope.status),
        "the app refused the write: {}",
        String::from_utf8_lossy(&envelope.body)
    );
    let stored: serde_json::Value =
        serde_json::from_slice(&envelope.body).expect("the relay's JSON answer");
    assert_eq!(
        stored["eventId"], event_id,
        "the relay must report storing THIS event"
    );

    // The number a soak is counted in: the node's own durable watermark, read
    // back through the same challenged endpoint, after the packet.
    tokio::time::sleep(StdDuration::from_secs(1)).await;
    let after = fetch_claim_state(&edge, &account, &payer)
        .await
        .expect("claim-state after the write");
    println!(
        "watermark advanced: nonce {} -> {}, cumulative {} -> {}",
        before.nonce, after.nonce, before.cumulative, after.cumulative
    );
    assert_eq!(after.nonce, nonce, "the node recorded this claim's nonce");
    assert_eq!(
        after.cumulative - before.cumulative,
        u128::from(price),
        "the channel advanced by exactly the route's price"
    );
}
