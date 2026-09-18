# Annex B — Conformance Test Vectors (normative)

Normative annex to [`v0.1.md`](v0.1.md). The machine-readable form, containing
the **exact bytes of every case**, is [`vectors/v0.1.json`](vectors/v0.1.json);
both are normative, and if they ever disagree the JSON wins.

Every value here is real: the keys, hashes, and Ed25519 signatures are
reproducible from the published test seeds. The vectors were self-checked —
each signature verifies (or fails) exactly as stated.

> **Test keys are TEST ONLY.** Their seeds are published deliberately so the
> vectors can be regenerated. Never use this material for anything real.

## B.1 How to use these vectors

1. Implement a sender/receiver per `v0.1.md`.
2. Evaluate each **envelope case** as a receiver whose clock reads the
   **reference time** (B.2) and whose freshness window is the default
   (300 s). Where a case's `from` address is delegated, use the key records of
   the *sending* domain.
3. The **expected outcome is binding**: a conforming receiver MUST produce the
   stated status and error token for the stated input.
4. Cases marked *policy-conditional* depend on receiving policy; the stated
   outcome applies to the policy described in the note.
5. Evaluate each **rotation case** with the key-chain rules of §3, starting
   from the `prior_record` as the currently authoritative key.
6. A conforming **sender** MUST produce, for the inputs of a positive case,
   a body whose bytes equal the case's `body` — including member ordering,
   spacing, and base64.

## B.2 Reference time

| | |
|---|---|
| Reference time `T` | `1748736000` = 2025-06-01T00:00:00Z |
| Freshness window `W` | 300 s (the default of REQ-6.1.5) |

All freshness outcomes below assume a receiver whose clock reads `T`.

## B.3 Test identities

Four keys, from public test seeds (32 bytes each): K1 = `0x01`×32, K2 =
`0x02`×32, K3 = `0x03`×32, K4 = `0x04`×32.

| Address | Key | `kid` | Role |
|---|---|---|---|
| `alice@example.net` | K1 | `NHUPmL1Z/PyUbaRaqr6TOw==` | current signing key |
| `alice@example.net` | K2 | `ajgD1fBZkCocba+8m6Rykg==` | rotation successor (cross-signed by K1) |
| `alice@provider.example` | K3 | `ti6Gf6LzOv5i1daxZC4WIQ==` | delegated identity (`sub=alice`), current |
| `alice@provider.example` | K4 | `xblA7T9lw5GWXegpX8XSXw==` | delegated rotation successor (cross-signed by K3) |

Public keys (raw, base64):

```
K1  iojj3XQJ8ZX9UtstPLpdcspnCb8dlBIb83SIAbQPb1w=
K2  gTl3Dqh9F19Wo1Rmw0x+zMuNipG07jeiXfYPW4/Js5Q=
K3  7UkoxijRwsbq6QM4kFmVYSlZJzpcY/k2NsFGFKyHN9E=
K4  ypOsFwUYcHHWe4PH/w7+gQjo7EUwV113JoeTM9vavnw=
```

Key records (`_imp-key` TXT values; K1 and K3 are genesis records, K2 and K4
carry `sigprev`):

```
v=imp1;alg=ed25519;k=iojj3XQJ8ZX9UtstPLpdcspnCb8dlBIb83SIAbQPb1w=;kid=NHUPmL1Z/PyUbaRaqr6TOw==;nb=1735689600;na=1767225599

v=imp1;alg=ed25519;k=gTl3Dqh9F19Wo1Rmw0x+zMuNipG07jeiXfYPW4/Js5Q=;kid=ajgD1fBZkCocba+8m6Rykg==;nb=1746057600;na=1780271999;sigprev=u5p0uzRQSKl6PGldrd0+NxSsomwoA2M27DSU0yfaT9UCq4umsiHoZ0Wdai1LkfuL1WwoXG8F3YTinuLbL7P+Dg==

v=imp1;alg=ed25519;k=7UkoxijRwsbq6QM4kFmVYSlZJzpcY/k2NsFGFKyHN9E=;kid=ti6Gf6LzOv5i1daxZC4WIQ==;nb=1735689600;na=1767225599;sub=alice

v=imp1;alg=ed25519;k=ypOsFwUYcHHWe4PH/w7+gQjo7EUwV113JoeTM9vavnw=;kid=xblA7T9lw5GWXegpX8XSXw==;nb=1746057600;na=1780271999;sub=alice;sigprev=Xl/MPt+2baPlwCT+CZr4sSKqwX7TcHhgpvsbKyAtdAP/+mqnQQbpu+yuCKbM349buh1pMteBsx5207piqnUzAw==
```

## B.4 Canonical serialization — worked example (case V1)

The signature input (REQ-4.8: canonical serialization with `sig` removed):

```
{"from":"alice@example.net","kid":"NHUPmL1Z/PyUbaRaqr6TOw==","msgid":"MDEyMzQ1Njc4OWFiY2RlZg==","payload":"aGVsbG8sIGltcA==","to":["bob@example.org"],"ts":1748735900,"type":"notification","v":1}
```

The body actually transmitted (REQ-5.3: canonical serialization including
`sig`; `sig` sorts between `payload` and `to`):

```
{"from":"alice@example.net","kid":"NHUPmL1Z/PyUbaRaqr6TOw==","msgid":"MDEyMzQ1Njc4OWFiY2RlZg==","payload":"aGVsbG8sIGltcA==","sig":"SXVgNd1kHovwNFedBgfviu8x/LD7T9uRpzgmUrShBrJqfX71lzkT/5kvFdK1SzMe5JCqhbRQfexPODDiSe0MDA==","to":["bob@example.org"],"ts":1748735900,"type":"notification","v":1}
```

Notes for implementers:

- Members are sorted by *name*: `from < kid < msgid < payload < sig < to < ts
  < type < v`. (`to` before `ts` before `type`; `v` last.)
- No whitespace, integers in minimal decimal, base64 standard **with**
  padding.
- `MDEyMzQ1Njc4OWFiY2RlZg==` is the 16 test bytes `0123456789abcdef`;
  `aGVsbG8sIGltcA==` is the payload `hello, imp`.

## B.5 Envelope cases

Exact bytes for every case are in `vectors/v0.1.json` (`body` and
`signature_input`). Every case below except V11 and V12 is a sealed envelope
produced with the stated key.

**`msgid` discipline.** Every *accepted* case carries a distinct `msgid`
(REQ-4.3). **V2** is the deliberate byte-identical duplicate of V1. The
*rejected* cases reuse V1's `msgid`, which additionally tests the gate order:
a receiver that checks replay before authenticating returns `409` where the
vector expects `401`/`410`/`505`/`422`.

| ID | Input | Expected | Token |
|---|---|---|---|
| **V1** | Valid notification from `alice@example.net`, K1, `ts = T−100` | `202 Accepted` | — |
| **V2** | Byte-identical resend of V1 after V1 was accepted | `409` | `duplicate` |
| **V3** | V1 plus member `"x_future":"ignored"`, signed | `202` | — |
| **V4** | V1 with `"type":"weird"`, signed | `202` | — |
| **V5** | V1 from `alice@provider.example` signed by K3 (`sub=alice` record) | `202` | — |
| **V6** | V1 plus `"in_reply_to"` set, signed | `202` | — |
| **V7** | V1 with `"v":99`, signed | `505` | `version_unsupported` |
| **V8** | V1 with the `payload` string replaced, **original signature kept** | `401` | `sig_invalid` |
| **V9** | V1 with `ts = 1767225600` (past K1's `na`), signed | `410` | `key_expired` |
| **V10** | V1 with `kid = "QkJCQkJCQkJCQkJCQkJCQg=="` (unpublished), signed | `403` | `key_unknown` |
| **V11** | V1's body with a space inserted after every `:` and `,` | `400` | `malformed` |
| **V12** | V1's body with a second `"from":"mallory@evil.example"` inserted | `400` | `malformed` |
| **V13** | V1 with `ts = T−1000` (stale; epoch still covers it), signed | `422` | `stale` |
| **V14** | V1, but the receiver's policy denies this sender *(policy-conditional)* | `403` | `not_permitted` |
| **V15** | V1 addressed to `carol@example.org` instead of the receiver's own address, signed | `403` | `not_permitted` |
| **V16** | V1 with `kid` set to the base64 of 8 bytes, signed | `400` | `malformed` |

Points the cases are designed to prove:

- **V3** demonstrates *rules not bytes*: `x_future` is covered by the
  signature and must be tolerated without being interpreted.
- **V4** demonstrates that verification is independent of `type` (REQ-4.12).
- **V6** demonstrates that a reserved member is ignored, not rejected
  (REQ-4.6).
- **V9** and **V13** together pin the **gate order**: the epoch check
  (REQ-6.1.3) precedes the freshness check (REQ-6.1.5), so a message that is
  both out-of-epoch and stale yields `410`, not `422`.
- **V11** is the strict-canonicalization case: a lenient receiver that
  re-serialized before verifying would accept it; a conforming receiver MUST
  reject it (B.7).
- **V14** shows that a policy refusal is a distinguishable, machine-readable
  answer (REQ-5.11), never a silent discard.

## B.6 Rotation cases

| ID | Input | Expected |
|---|---|---|
| **R1** | K2 record, `sigprev` by K1, overlapping epochs, distinct `kid` | accept |
| **R2** | K2 record whose `sigprev` is signed by K2 instead of K1 | reject |
| **R3** | K2-equivalent record with `nb = 1767225600 > K1.na` (no overlap) | reject |
| **R4** | A record re-publishing K1's `kid` as K1's successor (key id reused) | reject |
| **R5** | K4 record (`sub=alice`), `sigprev` by K3 — `sub` included in signed bytes | accept |

`R1` and `R5` are the two positive cases; `R2`–`R4` isolate one failure each
(bad cross-signature, non-overlap, key-id reuse). For `R3` and `R4` the
`sigprev` signature is **valid** — a receiver must reject them on the rotation
rules alone (`[SEC-4]`, `[SEC-5]`).

## B.7 Strict canonicalization (binding clarification)

A receiver **MUST NOT** re-serialize a body in order to verify it. The
received body MUST be byte-identical to the canonical serialization of its
members (REQ-4.7); otherwise the message is `400 malformed`, even when a
lenient re-serialization would verify. Consequences:

- Insignificant whitespace is malformed (V11).
- A repeated member name is malformed (V12) — there is no canonical ordering
  for a name that occurs twice.
- A sender MUST transmit the canonical bytes of REQ-4.7, unmodified
  (REQ-5.3).

Rationale: re-serialization is ambiguous (duplicate names, escaping choices),
and ambiguity in the signed bytes is exactly the class of bug this annex
exists to prevent.

## B.8 Coverage map

| Vector(s) | Requirements exercised |
|---|---|
| V1 | REQ-4.2, REQ-4.7, REQ-4.8, REQ-5.3, REQ-6.1 |
| V2 | REQ-4.3, REQ-5.7, REQ-6.1.6 |
| V3 | REQ-4.7, REQ-7.3 |
| V4 | REQ-4.11, REQ-4.12 |
| V5 | REQ-2.6, REQ-2.9 |
| V6 | REQ-4.6 |
| V7 | REQ-6.1.1, REQ-7.1, REQ-7.2 |
| V8 | REQ-4.8, REQ-6.1.4 |
| V9 | REQ-2.10.3, REQ-3.3, REQ-6.1.3 |
| V10 | REQ-2.10.2, REQ-6.1.3 |
| V11, V12 | REQ-4.7, REQ-6.1.2 |
| V13 | REQ-6.1.5 |
| V14 | REQ-5.11 |
| V15 | REQ-6.5 |
| V16 | REQ-4.13 |
| R1–R5 | REQ-2.8, REQ-3.2, REQ-3.3, REQ-3.4, REQ-3.5 |
