# IMP — IMP Message Protocol

**Status:** v0.1 draft, pre-freeze — the wire format may still change. The
contract is [`protocol/spec/v0.1.md`](protocol/spec/v0.1.md).

A self-hosted-first messaging protocol that replaces email's
reputation-based deliverability with **cryptographic identity**, so independent
servers can send to each other without building reputation over time and apps
can self-host their transactional messaging instead of relying on SaaS relays
(e.g. Resend).

This repository contains **only protocol material**:

| Path | Contents |
|------|----------|
| `protocol/spec/` | The protocol contract — **`v0.1.md`** (normative), its conformance vectors, and the extension registry |
| `protocol/formal/` | Lean 4 formalization machine-checking the security goals |
| `CITATION.cff` | How to cite this specification |

## Reading order

The contract is **`protocol/spec/v0.1.md`** — identity, rotation, envelope,
delivery, receiver verification, compatibility, and conformance — with its
normative test vectors in `protocol/spec/conformance.md` (Annex B) and
`protocol/spec/vectors/v0.1.json`, and its extension-point rules in
`protocol/spec/registry.md`.

## Building the formalization

Requires Lean 4 (v4.29.1, see `protocol/formal/lean-toolchain`):

```sh
cd protocol/formal
lake build +Imp
```

Checks all five modules and their theorems (`lake build` alone builds default
targets only — the library needs the explicit `+Imp` target).

IMP has a verified-clean collision record: no protocol or major software
trademark in the same space.

## License

Split to match what each file is:

- `protocol/spec/` — the protocol contract — **CC0 1.0 Universal** (public
  domain dedication; see `protocol/spec/LICENSE`). The contract belongs to
  everyone.
- `protocol/formal/` — the Lean formalization — **MIT** (see
  `protocol/formal/LICENSE`). Permissive for all use, no copyleft.

Patents: no patents are asserted; MIT's implicit grant posture is kept
deliberately simple for v1.
