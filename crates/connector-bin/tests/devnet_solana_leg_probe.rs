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

/// Whether `destination` is a blob-storage (`.ario`/`.store`) route rather than
/// a relay one.
///
/// Matched as a dot-separated SEGMENT, not a suffix. Size-tiered routes append
/// their own suffix -- `g.drew.ario.xl` is still an ario route -- and a
/// `ends_with` test silently misclassified them, which is expensive twice over:
/// the wrong envelope target (see [`target`]) and the wrong job body (see
/// [`job_body_for`]). Both failure modes are F00s that the payer is charged in
/// full for (connector#869), so this predicate is the single place to get it
/// right.
fn is_blob_route(destination: &str) -> bool {
    destination
        .split('.')
        .any(|segment| segment == "ario" || segment == "store")
}

/// The envelope target, defaulted BY ROUTE because the two routes want
/// opposite things and getting it wrong is an F00 that reads like a client
/// bug:
///
///   * a relay route's `handler_url` is `http://relay:3100` and the app
///     serves `POST /write`, so the target must be `/write`;
///   * an `.ario`/`.store` route's `handler_url` already ends in `/store`,
///     and `resolve_target_under_handler` appends the target BENEATH it --
///     so an absolute `/write` is refused outright (issue #621) and `""`,
///     meaning "the route's own handler path", is what a client with exactly
///     one endpoint sends.
///
/// Read with `var` rather than [`env`] so that an explicitly empty
/// `SOLANA_PROBE_TARGET=""` is honoured as the meaningful value it is, not
/// discarded as absent.
fn target() -> String {
    match std::env::var("SOLANA_PROBE_TARGET") {
        Ok(value) => value,
        Err(_) => {
            if is_blob_route(&destination()) {
                String::new()
            } else {
                "/write".to_string()
            }
        }
    }
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

/// The cluster the claim declares, derived from the RPC URL rather than
/// written as a literal.
///
/// This was `"devnet"` hardcoded in the claim body, which is a footgun the
/// node does not catch: `parse_solana` validates `cluster` only against the
/// fixed list `["mainnet-beta", "devnet", "testnet", "localnet"]` and never
/// against the chain the node is actually configured for
/// (`crates/connector-domain/src/client_claim.rs`). So a probe pointed at
/// mainnet with a stale literal here produces a claim that is accepted in
/// full while misdescribing which chain the payment happened on -- the one
/// thing a payment record must not do. Deriving it from `SOLANA_PROBE_RPC`
/// makes the two impossible to disagree.
fn cluster() -> String {
    if let Some(value) = env("SOLANA_PROBE_CLUSTER") {
        return value;
    }
    let url = env("SOLANA_PROBE_RPC").unwrap_or_else(|| DEFAULT_RPC_URL.to_string());
    if url.contains("mainnet") {
        "mainnet-beta".to_string()
    } else if url.contains("testnet") {
        "testnet".to_string()
    } else if url.contains("devnet") {
        "devnet".to_string()
    } else {
        "localnet".to_string()
    }
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
            "cluster": "{cluster}"
        }}"#,
        // `Z`, not `+00:00` -- the claim gate refuses the offset spelling by
        // name, and `chrono`'s plain `to_rfc3339()` emits exactly that.
        timestamp = Utc::now().to_rfc3339_opts(SecondsFormat::Millis, true),
        signer = payer.pubkey(),
        program = program_id(),
        channel = channel_account,
        cluster = cluster(),
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

/// Where this node's BTP door is, for a route whose policy requires that
/// carriage (issue #701).
///
/// **Derived, because the greeting does not carry it.** #807 added
/// `extra.btpEndpoint`, but the live devnet greeting for a `transport = "btp"`
/// route advertises `requiredTransport: "btp"` and no URL to satisfy it with --
/// the same gap `connector-cli/src/announce.rs` documents and guesses around.
/// `wss://<host>/ilp/btp` is the deployed convention, and it is a guess; the
/// override exists so a node that spells it differently is reachable without a
/// rebuild.
fn btp_url(edge: &str) -> String {
    env("SOLANA_PROBE_BTP_URL").unwrap_or_else(|| {
        format!(
            "{}/ilp/btp",
            edge.replacen("https://", "wss://", 1)
                .replacen("http://", "ws://", 1)
        )
    })
}

/// One paid packet over a BTP session, for a route that refuses HTTP.
///
/// Modelled on `announce.rs`'s `send_over_btp` and using the same
/// [`connector_btp`] codec both roles share (ADR 0027) -- never a second
/// hand-rolled frame.
///
/// **The claim is RAW JSON here, not base64.** That is the one substantive
/// difference between the two carriages: over HTTP the header value is
/// base64 of the claim JSON, and over BTP the `payment-channel-claim`
/// protocolData carries the JSON bytes themselves. Base64-ing it here
/// produces a claim the far side cannot parse, which is refused exactly like
/// a malformed one.
async fn deliver_over_btp(
    btp_url: &str,
    prepare: &Prepare,
    claim: &str,
) -> Result<Fulfill, String> {
    use futures_util::{SinkExt, StreamExt};
    use tokio_tungstenite::tungstenite::Message;

    const REQUEST_ID: u32 = 1;

    let (mut socket, _response) = tokio::time::timeout(
        StdDuration::from_secs(20),
        tokio_tungstenite::connect_async(btp_url),
    )
    .await
    .map_err(|_| format!("timed out opening {btp_url}"))?
    .map_err(|error| format!("could not open {btp_url}: {error}"))?;

    let frame = connector_btp::encode_message(
        REQUEST_ID,
        &[connector_btp::ProtocolData {
            name: connector_btp::CLAIM_PROTOCOL.to_string(),
            content_type: connector_btp::CONTENT_TYPE_TEXT,
            data: claim.as_bytes().to_vec(),
        }],
        &prepare.encode(),
    );
    socket
        .send(Message::Binary(frame))
        .await
        .map_err(|error| format!("send: {error}"))?;

    // The session's own advertised lease is 120s; this is one packet, so a
    // shorter ceiling is honest -- a far side that has not answered by now is
    // not going to.
    let answer = tokio::time::timeout(StdDuration::from_secs(60), async {
        while let Some(message) = socket.next().await {
            let bytes = match message.map_err(|error| format!("recv: {error}"))? {
                Message::Binary(bytes) => bytes,
                Message::Close(_) => return Err("the session closed before answering".to_string()),
                _ => continue,
            };
            let decoded = connector_btp::decode_frame(&bytes)
                .map_err(|error| format!("undecodable frame: {error:?}"))?;
            if decoded.request_id != REQUEST_ID {
                continue;
            }
            return Ok(decoded);
        }
        Err("the session ended without answering".to_string())
    })
    .await
    .map_err(|_| "no answer within 60s".to_string())??;

    let _ = socket.close(None).await;

    if answer.frame_type == connector_btp::BTP_ERROR {
        return Err(format!(
            "BTP ERROR: {}",
            String::from_utf8_lossy(&answer.ilp_packet)
        ));
    }
    // The BTP twin of the HTTP 402: the identical x402 terms bytes ride as
    // `payment-required` protocolData on a REJECT.
    if let Some(terms) = answer
        .protocol_data
        .iter()
        .find(|entry| entry.name == connector_btp::PAYMENT_REQUIRED_PROTOCOL)
    {
        return Err(format!(
            "still unpaid -- x402 terms came back: {}",
            String::from_utf8_lossy(&terms.data)
                .chars()
                .take(300)
                .collect::<String>()
        ));
    }
    if let Ok(fulfill) = Fulfill::decode(&answer.ilp_packet) {
        return Ok(fulfill);
    }
    match Reject::decode(&answer.ilp_packet) {
        Ok(reject) => Err(format!(
            "REJECTED {:?} {}: {}",
            reject.code, reject.triggered_by, reject.message
        )),
        Err(_) => Err("neither a FULFILL nor a REJECT".to_string()),
    }
}

/// What transport `destination` requires, from the node's own greeting -- so a
/// probe never has to be told, and a route that flips to BTP later does not
/// silently start failing.
async fn required_transport(edge: &str, destination: &str, target: &str) -> Option<String> {
    let identity = fetch_identity(edge).await;
    let (prepare, _secret) = sealed_prepare(
        fetch_price(edge, destination).await,
        destination,
        target,
        b"{}",
        &identity,
    );
    let response = reqwest::Client::new()
        .post(format!("{edge}/ilp"))
        .body(prepare.encode())
        .send()
        .await
        .expect("POST /ilp unpaid");
    let terms: serde_json::Value = response.json().await.ok()?;
    terms["accepts"][0]["extra"]["requiredTransport"]
        .as_str()
        .map(str::to_string)
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

/// NIP-90 Arweave blob-storage job (`@toon-protocol/core`'s
/// `buildBlobStorageRequest`) -- what an `.ario`/`.store` route's app wants,
/// as opposed to a relay's `{"event": <kind:1>}`.
///
/// Sending the wrong one of these two is not a loud failure. Under ADR 0020 a
/// non-2xx from the app is a real answer that consumed real work, so it rides
/// home on a FULFILL carrying `status: 422` and the payer is charged in full
/// for nothing. That is why [`job_body_for`] picks by route rather than
/// leaving it to the caller to remember.
const BLOB_STORAGE_REQUEST_KIND: u64 = 5094;

fn signed_blob_storage_job(
    blob: &[u8],
    content_type: &str,
    bid: u64,
) -> (serde_json::Value, String) {
    use k256::schnorr::signature::hazmat::PrehashSigner;
    use k256::schnorr::SigningKey;
    use sha2::{Digest, Sha256};

    // A per-run key: this event is a receipt for one upload, never
    // republished, so a fixed key would only make two runs indistinguishable.
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&now_secs().to_be_bytes());
    seed[8..24].copy_from_slice(&Sha256::digest(blob)[..16]);
    seed[31] |= 1; // never the zero scalar
    let signing_key = SigningKey::from_bytes(&seed).expect("nostr signing key");
    let pubkey = hex_encode(&signing_key.verifying_key().to_bytes());
    let created_at = now_secs();

    let tags = serde_json::json!([
        ["i", BASE64.encode(blob), "blob"],
        ["bid", bid.to_string(), "usdc"],
        ["output", content_type],
    ]);
    let serialized =
        serde_json::json!([0, pubkey, created_at, BLOB_STORAGE_REQUEST_KIND, tags, ""]).to_string();
    let id = hex_encode(&Sha256::digest(serialized.as_bytes()));
    let signature: k256::schnorr::Signature = signing_key
        .sign_prehash(&hex_decode(&id))
        .expect("schnorr sign the event id");

    let event = serde_json::json!({
        "id": id,
        "pubkey": pubkey,
        "created_at": created_at,
        "kind": BLOB_STORAGE_REQUEST_KIND,
        "tags": tags,
        "content": "",
        "sig": hex_encode(&signature.to_bytes()),
    });
    (event, id)
}

/// NIP-90 ArNS brokered-buy job (kind:5095).
///
/// ⚠️ Its arguments are `["param", k, v]` tags, NOT the `["i", ...]` input tags
/// kind:5094 uses. The handler requires `name` and `processId`.
///
/// ⭐ **Omitting `processId` is the ZERO-ARIO validation mode.** The handler
/// parses the event, finds the required param missing, and refuses BY NAME
/// before it ever quotes or touches the ar.io registry. That proves the entire
/// paid path (settlement, routing, envelope, event signature, handler dispatch)
/// without moving a single $ARIO, which is the only safe way to rehearse a job
/// that otherwise spends real money on a real registry.
const ARNS_BUY_REQUEST_KIND: u64 = 5095;

fn signed_arns_buy_job(
    name: &str,
    process_id: Option<&str>,
    buy_type: &str,
    years: Option<u32>,
    bid: u64,
) -> (serde_json::Value, String) {
    use k256::schnorr::signature::hazmat::PrehashSigner;
    use k256::schnorr::SigningKey;
    use sha2::{Digest, Sha256};

    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&now_secs().to_be_bytes());
    seed[8..24].copy_from_slice(&Sha256::digest(name.as_bytes())[..16]);
    seed[31] |= 1;
    let signing_key = SigningKey::from_bytes(&seed).expect("nostr signing key");
    let pubkey = hex_encode(&signing_key.verifying_key().to_bytes());
    let created_at = now_secs();

    let mut tag_list = vec![
        serde_json::json!(["param", "name", name]),
        serde_json::json!(["param", "type", buy_type]),
        serde_json::json!(["bid", bid.to_string(), "usdc"]),
    ];
    if let Some(pid) = process_id {
        tag_list.push(serde_json::json!(["param", "processId", pid]));
    }
    if let Some(y) = years {
        tag_list.push(serde_json::json!(["param", "years", y.to_string()]));
    }
    let tags = serde_json::Value::Array(tag_list);

    let serialized =
        serde_json::json!([0, pubkey, created_at, ARNS_BUY_REQUEST_KIND, tags, ""]).to_string();
    let id = hex_encode(&Sha256::digest(serialized.as_bytes()));
    let signature: k256::schnorr::Signature = signing_key
        .sign_prehash(&hex_decode(&id))
        .expect("schnorr sign the event id");

    let event = serde_json::json!({
        "id": id,
        "pubkey": pubkey,
        "created_at": created_at,
        "kind": ARNS_BUY_REQUEST_KIND,
        "tags": tags,
        "content": "",
        "sig": hex_encode(&signature.to_bytes()),
    });
    (event, id)
}

/// How many KiB the blob-storage job should carry, from `SOLANA_PROBE_BLOB_KB`.
///
/// Exists to cross AR.IO's free-tier boundary deliberately, so the store's PAID
/// upload path is exercised rather than only the ILP leg. The boundary is not
/// the commonly quoted "100 KB": AR.IO's own service descriptor reports
/// `freeUploadLimitBytes: 107520` with `freeTier.maxItemBytes: 107520`, plus
/// CUMULATIVE `lifetimeBytes` and `ipBytes` of 10485760 each. So a single item
/// must exceed 105 KiB to be charged for, and separately a wallet or a source
/// IP stops being free forever after 10 MiB in total.
///
/// Default 0 = the note alone, which keeps every existing invocation
/// byte-identical.
fn blob_kb() -> usize {
    match env("SOLANA_PROBE_BLOB_KB") {
        Some(value) => value
            .parse()
            .expect("SOLANA_PROBE_BLOB_KB is a whole number of KiB"),
        None => 0,
    }
}

/// A file whose bytes become the blob verbatim, from `SOLANA_PROBE_BLOB_FILE`.
///
/// `SOLANA_PROBE_BLOB_KB` pads a note with dots, which proves the paid path but
/// stores nothing anyone would want to read back. This carries a real artifact
/// instead -- an HTML page, an image, a manifest -- so the thing on Arweave is
/// worth resolving an ArNS name at.
///
/// Takes precedence over `SOLANA_PROBE_BLOB_KB` when both are set: a caller who
/// named a file meant that file, and silently appending dots to it would
/// corrupt any format with a trailing structure. Unset, behaviour is unchanged.
fn blob_file() -> Option<Vec<u8>> {
    let path = env("SOLANA_PROBE_BLOB_FILE")?;
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|err| panic!("SOLANA_PROBE_BLOB_FILE {path} is unreadable: {err}"));
    assert!(
        !bytes.is_empty(),
        "SOLANA_PROBE_BLOB_FILE {path} is empty -- refusing to pay to store nothing"
    );
    Some(bytes)
}

/// The blob's `output` content type, from `SOLANA_PROBE_BLOB_CONTENT_TYPE`.
///
/// The store forwards this onto the Arweave upload's Content-Type, so it is
/// what decides whether a gateway serves the item as a page or offers it as a
/// download. Defaults to `text/plain`, which is what every prior run sent.
fn blob_content_type() -> String {
    env("SOLANA_PROBE_BLOB_CONTENT_TYPE").unwrap_or_else(|| "text/plain".to_string())
}

/// The self-describing note, padded out to `kb` KiB.
///
/// The note stays at the FRONT so the artifact still names its own channel and
/// nonce to anyone who fetches it -- padding must not cost the payload its
/// third-party verifiability.
fn padded_blob(note: &str, kb: usize) -> Vec<u8> {
    let mut blob = note.as_bytes().to_vec();
    let target = kb * 1024;
    if blob.len() < target {
        blob.push(b'\n');
        blob.resize(target, b'.');
    }
    blob
}

/// The right body for `destination`, and the field of the app's answer that
/// names what it did with it. An `.ario`/`.store` route gets a kind:5094
/// blob-storage job; anything else gets a relay write.
///
/// Routing decided by [`is_blob_route`] -- see there for why a suffix test was
/// wrong. Under ADR 0020 misclassifying is not a loud failure: the app's 422
/// rides home on a FULFILL and the payer is charged in full for nothing.
fn job_body_for(destination: &str, note: &str, price: u64) -> (Vec<u8>, String, &'static str) {
    if is_blob_route(destination) {
        // kind:5095 takes precedence on a blob route when a name is named.
        // ⚠️ SPENDS REAL $ARIO on a real registry when ARNS_PROBE_PROCESS_ID is
        // also set. Without it, the handler refuses by name and nothing moves.
        if let Some(name) = env("ARNS_PROBE_NAME") {
            let process_id = env("ARNS_PROBE_PROCESS_ID");
            let buy_type = env("ARNS_PROBE_TYPE").unwrap_or_else(|| "lease".to_string());
            let years = env("ARNS_PROBE_YEARS").and_then(|y| y.parse::<u32>().ok());
            let (event, id) =
                signed_arns_buy_job(&name, process_id.as_deref(), &buy_type, years, price);
            let field = if process_id.is_some() {
                "arnsResult"
            } else {
                "arnsRefusal"
            };
            return (write_body(&event), id, field);
        }
        let blob = match blob_file() {
            Some(bytes) => bytes,
            None => padded_blob(note, blob_kb()),
        };
        let (event, id) = signed_blob_storage_job(&blob, &blob_content_type(), price);
        (write_body(&event), id, "txId")
    } else {
        let (event, id) = signed_nostr_event(note);
        (write_body(&event), id, "eventId")
    }
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

// ── 1b. discovering a node's Solana settlement address ───────────────────────

/// The node's own x402 greeting (client-edge-spec.md §1.4), which is how a
/// client that has never met this node learns WHERE to open a channel: the
/// settlement address is `key_file`-backed and therefore appears in no config
/// a stranger could read.
///
/// The greeting answers an UNPAID request to a priced route, so this costs
/// nothing -- but the request must still be a well-formed `Prepare`, or the
/// edge answers "buffer underflow: packet is truncated" rather than terms.
/// That is the whole trap: an empty POST looks like a broken node.
#[tokio::test]
async fn the_nodes_greeting_names_where_to_open_a_solana_channel() {
    let Some(edge) = edge() else {
        return;
    };
    let destination = destination();
    let identity = fetch_identity(&edge).await;
    let (prepare, _secret) = sealed_prepare(
        fetch_price(&edge, &destination).await,
        &destination,
        &target(),
        b"{}",
        &identity,
    );

    let response = reqwest::Client::new()
        .post(format!("{edge}/ilp"))
        .body(prepare.encode())
        .send()
        .await
        .expect("POST /ilp unpaid");
    assert_eq!(
        response.status(),
        reqwest::StatusCode::PAYMENT_REQUIRED,
        "an unpaid request to a priced route is answered with x402 terms"
    );
    let terms: serde_json::Value = response.json().await.expect("x402 terms json");
    println!(
        "{}",
        serde_json::to_string_pretty(&terms).expect("pretty terms")
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
    let (body, job_id, answer_field) = job_body_for(&destination, &content, price);
    let (prepare, secret) = sealed_prepare(price, &destination, &target(), &body, &identity);

    // Which carriage this route accepts is the node's decision, not this
    // probe's, so it is read from the greeting rather than configured here --
    // a route that flips to BTP later keeps working instead of silently
    // failing with a 402 that looks like an unpaid packet.
    let transport = required_transport(&edge, &destination, &target()).await;
    let fulfill = match transport.as_deref() {
        Some("btp") => {
            let url = btp_url(&edge);
            println!("route requires BTP -- delivering over {url}");
            deliver_over_btp(&url, &prepare, &claim)
                .await
                .unwrap_or_else(|error| panic!("{error}"))
        }
        _ => {
            let response = reqwest::Client::new()
                .post(format!("{edge}/ilp"))
                .header(CLAIM_HEADER, BASE64.encode(claim.as_bytes()))
                .body(prepare.encode())
                .send()
                .await
                .expect("POST /ilp");
            assert_eq!(response.status(), reqwest::StatusCode::OK);
            let body = response.bytes().await.expect("response body");
            // A REJECT decodes first so a failure names itself, rather than
            // surfacing as an opaque "could not decode a Fulfill".
            if let Ok(reject) = Reject::decode(&body) {
                panic!(
                    "REJECTED {:?} {}: {}",
                    reject.code, reject.triggered_by, reject.message
                );
            }
            Fulfill::decode(&body).expect("a Fulfill")
        }
    };
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
    // ⭐ The zero-ARIO ArNS rehearsal INVERTS the usual expectation: a refusal
    // is the pass. The packet was paid for and delivered, and the handler got
    // far enough to parse the event and find `processId` missing. Asserting
    // 2xx here would report a successful rehearsal as a failure.
    if answer_field == "arnsRefusal" {
        let body = String::from_utf8_lossy(&envelope.body);
        assert!(
            !(200..300).contains(&envelope.status),
            "a 5095 job with no processId must be REFUSED, not accepted: {body}"
        );
        assert!(
            body.contains("processId"),
            "the handler must refuse for the missing processId specifically, \
             not for some earlier failure that would prove nothing: {body}"
        );
        println!(
            "ZERO-ARIO REHEARSAL PASSED -- paid, routed, and refused by name \
             (status {}). No $ARIO moved.",
            envelope.status
        );
        return;
    }

    assert!(
        (200..300).contains(&envelope.status),
        "the app refused the write: {}",
        String::from_utf8_lossy(&envelope.body)
    );
    let stored: serde_json::Value =
        serde_json::from_slice(&envelope.body).expect("the app's JSON answer");
    if answer_field == "arnsResult" {
        println!("ArNS receipt: {}", stored["result"]);
        assert!(
            stored["result"]["registryTxId"]
                .as_str()
                .is_some_and(|id| !id.is_empty()),
            "a real ArNS buy must answer with a registry tx id: {stored}"
        );
        return;
    }
    // A relay names the event id it stored; an ario/store app names the
    // Arweave tx id it minted. Either way the answer is the app's own word
    // about work it did, not this probe's about a packet it sent.
    if answer_field == "eventId" {
        assert_eq!(
            stored["eventId"], job_id,
            "the relay must report storing THIS event"
        );
    } else {
        println!("stored on Arweave: {}", stored["txId"]);
        assert!(
            stored["txId"].as_str().is_some_and(|id| !id.is_empty()),
            "the store app must answer with a real Arweave tx id: {stored}"
        );
    }

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

// ── 5. the channel lifecycle: redeem on chain, close, settle ─────────────────

/// The three paths `toon-meta/docs/soak-criteria.md` §1 records as **not yet
/// observed** for the Solana family: a claim redeemed on chain, a channel
/// closed, and a vault settled back to its participants. Nothing has ever been
/// redeemed on chain on any TOON chain, and no Solana channel has ever been
/// closed, which is exactly why that family's soak clock has not started.
///
/// Gated on `SOLANA_PROBE_LIFECYCLE=1`, separately from every other gate in
/// this file, because it is the only test here that **ends** a channel. Every
/// other path is repeatable; this one is not, and against mainnet it moves
/// real money.
///
/// ## Resumable by design
///
/// `SettleChannel` cannot run until the challenge window elapses:
/// `process_settlement` rejects with `ChannelChallengeNotExpired` until
/// `close_timestamp + challenge_duration`, which is 3600s on a channel opened
/// with this probe's default. Rather than hold a test process open for an
/// hour, each phase reads the chain and skips whatever is already done -- so
/// the same command, run twice about an hour apart, walks the channel through
/// the whole lifecycle and prints one transaction signature per phase.
///
/// ## Why the payer can do all three alone
///
/// The payer is the `claimer` of its own balance proof even though the credit
/// ultimately flows to the node. `process_claim_from_channel` records
/// `transferred_amount` against whichever participant's signature the Ed25519
/// precompile verified, and settlement pays out
/// `deposit_x - transferred_x + transferred_y`. The node never signs anything
/// here: per the account-list comment at `processor.rs:671-675`, the fee-payer
/// is deliberately decoupled from the claiming participant. `CloseChannel`
/// requires a signer that is *a* participant, and `SettleChannel` requires only
/// a signer. So none of this needs the node's settlement key.
///
/// ## What it redeems
///
/// Not a nonce and amount written here, but the ones the **node** says it
/// accepted, read back from `/ilp/claim-state`. Redeeming anything else would
/// put the chain and the node's own durable watermark into disagreement, and
/// the watermark is the number the soak bar is counted in. Override with
/// `SOLANA_PROBE_CLAIM_NONCE` + `SOLANA_PROBE_CLAIM_UNITS` only when the node
/// is unreachable and the values are known from elsewhere.
#[tokio::test]
async fn redeem_close_and_settle_this_channel() {
    let (Some(edge), Some(node), Some(payer)) = (edge(), node_pubkey(), payer()) else {
        return;
    };
    if env("SOLANA_PROBE_LIFECYCLE").is_none() {
        return;
    }
    // `SOLANA_PROBE_DRY_RUN=1` prints what each phase would submit and signs
    // nothing. Worth having on the one path in this file that cannot be re-run:
    // the cost of being wrong here is not a wasted minute, it is a channel
    // closed early or a claim redeemed at the wrong nonce.
    let dry_run = env("SOLANA_PROBE_DRY_RUN").is_some();
    if dry_run {
        println!("── DRY RUN: reading chain state and reporting the plan, signing nothing ──");
    }
    let client = rpc();
    let mint = mint();
    let program = program_id();
    let payer_pubkey = payer.pubkey();

    let (account, channel) = read_channel(&client, &payer_pubkey, &node, &mint).await;
    let Some(channel) = channel else {
        // A settled channel's account is zeroed and deallocated by the program
        // itself, so "never existed" and "already settled" are indistinguishable
        // from chain (`wire::ChannelAccount::parse`'s own doc says so). Report
        // both rather than calling a finished lifecycle a broken node.
        println!(
            "channel {account} does not exist on chain -- either it was never opened, or it \
             has already been settled and the program deallocated its account"
        );
        return;
    };

    let status = channel.parsed.status;
    println!(
        "channel {account}\n  status={status:?} challenge={}s\n  \
         deposit_a={} transferred_a={} nonce_a={}\n  \
         deposit_b={} transferred_b={} nonce_b={}",
        channel.parsed.challenge_duration,
        channel.parsed.deposit_a,
        channel.parsed.transferred_amount_a,
        channel.parsed.nonce_a,
        channel.parsed.deposit_b,
        channel.parsed.transferred_amount_b,
        channel.parsed.nonce_b,
    );

    let payer_is_a = channel.parsed.participant_a == payer_pubkey;
    assert!(
        payer_is_a || channel.parsed.participant_b == payer_pubkey,
        "this keypair is not a participant of {account} -- it cannot close or claim on it"
    );
    let (stored_nonce, stored_transferred) = if payer_is_a {
        (channel.parsed.nonce_a, channel.parsed.transferred_amount_a)
    } else {
        (channel.parsed.nonce_b, channel.parsed.transferred_amount_b)
    };

    // What phase 1 redeems, remembered so phase 3 can project it into the
    // payout it reports. Without this a dry run reads the payout off an
    // account that has not been claimed against yet, and reports the recipient
    // receiving nothing -- which is the exact opposite of what the run proves.
    let mut planned_transferred: Option<u64> = None;

    // ── phase 1: ClaimFromChannel ────────────────────────────────────────────
    //
    // Allowed while the channel is Opened OR Closed (`processor.rs:731-741`
    // rejects only Settled), so a claim missed before the close can still be
    // redeemed during the challenge window -- which is the entire point of
    // having one.
    if status != wire::ChannelStatus::Settled {
        let target = match (
            env("SOLANA_PROBE_CLAIM_NONCE"),
            env("SOLANA_PROBE_CLAIM_UNITS"),
        ) {
            (Some(nonce), Some(units)) => Some((
                nonce
                    .parse::<u64>()
                    .expect("SOLANA_PROBE_CLAIM_NONCE is a u64"),
                units
                    .parse::<u64>()
                    .expect("SOLANA_PROBE_CLAIM_UNITS is a u64"),
            )),
            _ => fetch_claim_state(&edge, &account, &payer)
                .await
                .map(|state| {
                    let units = u64::try_from(state.cumulative)
                        .expect("the node's cumulative fits a u64 of base units");
                    (state.nonce, units)
                }),
        };

        match target {
            None => println!(
                "no claim state available from the node and no explicit override -- skipping \
                 the redemption phase rather than guessing a nonce"
            ),
            Some((nonce, units)) if nonce <= stored_nonce => println!(
                "nothing to redeem: the node's claim (nonce {nonce}, {units} units) is not \
                 ahead of the chain's stored nonce {stored_nonce} -- already redeemed"
            ),
            Some((nonce, units)) => {
                assert!(
                    units >= stored_transferred,
                    "refusing to submit a claim that decreases transferred_amount \
                     ({units} < {stored_transferred}): the program rejects it \
                     (TransferredAmountDecreased) and it would mean the node's watermark \
                     disagrees with the chain"
                );
                let deposit = channel.payer_deposit(&payer_pubkey);
                assert!(
                    units <= deposit,
                    "refusing to submit a claim above the payer's own deposit \
                     ({units} > {deposit}): the program bounds it there precisely so the \
                     channel stays settleable (`processor.rs`'s deposit bound)"
                );

                // Signed here rather than replayed from the node, because the node
                // stores what it verified, not the 64 signature bytes. Same key,
                // same message, so the precompile sees an identical proof.
                let message = wire::balance_proof_message(&account, nonce, units);
                let signature: [u8; 64] = payer
                    .sign_message(&message)
                    .as_ref()
                    .try_into()
                    .expect("an ed25519 signature is 64 bytes");

                planned_transferred = Some(units);
                println!("redeeming nonce {nonce}, {units} base units, on chain");
                if dry_run {
                    println!(
                        "   DRY RUN -- would submit ClaimFromChannel(nonce={nonce}, \
                         transferred={units}) for claimer {payer_pubkey}, behind an Ed25519 \
                         proof at instruction index 0"
                    );
                } else {
                    let tx = submit(
                        &client,
                        &payer,
                        &[
                            // Index 0 is not a style choice: `verify_ed25519_precompile`
                            // calls `load_instruction_at_checked(0, ..)`, so the proof
                            // must sit ahead of the instruction it authorizes.
                            wire::ed25519_verify_instruction(&payer_pubkey, &signature, &message),
                            Instruction::new_with_bytes(
                                program,
                                &wire::pack_claim_from_channel(nonce, units),
                                wire::Accounts::claim_from_channel(
                                    &payer_pubkey,
                                    &payer_pubkey,
                                    &account,
                                ),
                            ),
                        ],
                        "ClaimFromChannel",
                    )
                    .await;
                    println!("✅ ClaimFromChannel: {tx}");
                }
            }
        }
    }

    // ── phase 2: CloseChannel ────────────────────────────────────────────────
    if status == wire::ChannelStatus::Opened {
        println!("closing {account} -- this starts the challenge window and is not reversible");
        if dry_run {
            println!(
                "   DRY RUN -- would submit CloseChannel signed by {payer_pubkey}, starting a \
                 {}s challenge window before SettleChannel is permitted",
                channel.parsed.challenge_duration
            );
        } else {
            let tx = submit(
                &client,
                &payer,
                &[Instruction::new_with_bytes(
                    program,
                    &wire::pack_close_channel(),
                    wire::Accounts::close_channel(&payer_pubkey, &account),
                )],
                "CloseChannel",
            )
            .await;
            println!("✅ CloseChannel: {tx}");
        }
    }

    // ── phase 3: SettleChannel ───────────────────────────────────────────────
    //
    // Re-read rather than reusing the pre-close snapshot: `close_timestamp` is
    // written by the program from its own `Clock`, and it is what the deadline
    // below is computed from.
    let (_account, settled_view) = read_channel(&client, &payer_pubkey, &node, &mint).await;
    let Some(current) = settled_view else {
        println!("channel account is gone -- nothing left to settle");
        return;
    };
    let is_closed = current.parsed.status == wire::ChannelStatus::Closed;
    let deadline = current.parsed.close_timestamp + current.parsed.challenge_duration as i64;
    let remaining = deadline - now_secs() as i64;
    let settle_ready = is_closed && remaining <= 0;

    if !settle_ready {
        if is_closed {
            println!(
                "⏳ challenge window open for another {remaining}s ({}m). Settle is refused \
                 until then (ChannelChallengeNotExpired). Re-run this same command after that \
                 and it will pick up at the settle phase.",
                remaining / 60
            );
        } else {
            println!(
                "channel is {:?}, not Closed -- nothing to settle yet",
                current.parsed.status
            );
        }
        // A dry run deliberately keeps going here. The associated-token-account
        // pre-flight below is the most useful check available before any money
        // moves, and it does not depend on the channel already being closed --
        // so surfacing a missing ATA now is worth more than an early return.
        if !dry_run {
            return;
        }
    }

    // Both participants' associated token accounts must already exist: the
    // program transfers into them and does not create them. A missing node-side
    // ATA is the one failure here that looks like a program bug and is not, so
    // it is checked by name before anything is submitted.
    let payer_token =
        spl_associated_token_account::get_associated_token_address(&payer_pubkey, &mint);
    let node_token = spl_associated_token_account::get_associated_token_address(&node, &mint);
    for (owner, ata, label) in [
        (payer_pubkey, payer_token, "payer"),
        (node, node_token, "node"),
    ] {
        let exists = client
            .get_account_with_commitment(&ata, CommitmentConfig::confirmed())
            .await
            .expect("getAccountInfo")
            .value
            .is_some();
        assert!(
            exists,
            "the {label}'s associated token account {ata} (owner {owner}, mint {mint}) does \
             not exist. SettleChannel transfers into it and cannot create it, so settlement \
             would fail with an opaque token-program error. Create it first -- it is \
             permissionless and costs about 0.002 SOL: \
             `spl-token create-account {mint} --owner {owner} --fee-payer <your keypair>`"
        );
    }

    let (vault, _bump) = wire::vault_pda(&account, &program);
    let (participant_a_token, participant_b_token) = if payer_is_a {
        (payer_token, node_token)
    } else {
        (node_token, payer_token)
    };

    println!("✅ both associated token accounts exist -- settlement has somewhere to pay out to");

    // The payouts settlement will make, computed here from the same formula
    // `process_settlement` uses, so a dry run says what the money does rather
    // than only that it moves.
    // On a real run the claim has already landed, so the re-read account
    // carries it. On a dry run nothing was submitted and the account still
    // shows the pre-claim amounts, so the claim phase 1 planned is projected in
    // here. Reporting the unprojected figure would say the recipient receives
    // nothing, when crediting the recipient is the whole point of the exercise.
    let (transferred_a, transferred_b) = match planned_transferred {
        Some(units) if dry_run && payer_is_a => (units, current.parsed.transferred_amount_b),
        Some(units) if dry_run => (current.parsed.transferred_amount_a, units),
        _ => (
            current.parsed.transferred_amount_a,
            current.parsed.transferred_amount_b,
        ),
    };
    let balance_a = current.parsed.deposit_a - transferred_a + transferred_b;
    let balance_b = current.parsed.deposit_b - transferred_b + transferred_a;
    let basis = if planned_transferred.is_some() && dry_run {
        "payout at settle (projecting the claim above)"
    } else {
        "payout at settle"
    };
    println!(
        "{basis}: participant_a {participant_a_token} <- {balance_a}, \
         participant_b {participant_b_token} <- {balance_b} (base units)"
    );

    if !settle_ready {
        println!(
            "   DRY RUN -- would submit SettleChannel from vault {vault}, deallocating the \
             channel and vault accounts and returning their rent to {payer_pubkey}"
        );
        return;
    }

    println!("settling {account}: vault {vault} -> {participant_a_token} / {participant_b_token}");
    if dry_run {
        println!(
            "   DRY RUN -- would submit SettleChannel now (the challenge window has already \
             elapsed), deallocating the channel and vault accounts and returning their rent \
             to {payer_pubkey}"
        );
        return;
    }
    let tx = submit(
        &client,
        &payer,
        &[Instruction::new_with_bytes(
            program,
            &wire::pack_settle_channel(),
            wire::Accounts::settle_channel(
                &payer_pubkey,
                &account,
                &vault,
                &participant_a_token,
                &participant_b_token,
                // Rent recipient: the channel and vault accounts are deallocated
                // here and their rent has to land somewhere. It goes back to the
                // wallet that funded them.
                &payer_pubkey,
            ),
        )],
        "SettleChannel",
    )
    .await;
    println!("✅ SettleChannel: {tx}");
    println!(
        "channel {account} is settled. The account is now deallocated, so a later read of it \
         returns nothing -- that is success, not a missing channel."
    );
}
