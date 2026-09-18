# IMP Message Protocol — Specification

**The contract is [`v0.1.md`](v0.1.md).** It is the single normative document:
identity, rotation, envelope, delivery, receiver verification, compatibility,
and conformance, with every security-relevant requirement mapped to a Lean
theorem or a tracked open obligation.

License: CC0 1.0 Universal (see `LICENSE`).

## Documents

| File | Role |
|------|------|
| **`v0.1.md`** | **The protocol contract (normative).** |
| **`conformance.md`** | **Annex B — conformance test vectors (normative).** |
| **`registry.md`** | **Registry and registration procedure (normative, `REQ-R.*`).** |
| `vectors/v0.1.json` | Machine-readable vectors — exact bytes of every case (normative). |

The pre-v0.1 numbered drafts have been retired; they remain available in git
history and are the source of the `SEC-1`…`SEC-5` numbering.

## Conventions used in `v0.1.md`

- Keywords MUST, SHOULD, MAY follow RFC 2119.
- `REQ-x.y` are normative requirements; `SEC-n` are security goals.
- Proof references like `Imp.validate_ok_implies_sig` resolve to
  declarations under `../formal/`.
- *(impl obligation)* marks a deferred mechanical verification, with the
  obligation stated in §9 of the contract.
