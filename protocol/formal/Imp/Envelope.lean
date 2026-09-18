import Imp.Signature

/-!
# Imp.Envelope

The signed message format of `protocol/spec/v0.1.md` §4 (REQ-4.2 … REQ-4.10).

`canonical` is the projection the signature covers (REQ-4.7, REQ-4.8).
`envelope_eq_of_fields` pins the field-level injectivity of REQ-4.9 / SEC-2;
the byte-framing result is `Imp.body_injective` / `Imp.signatureInput_injective`
in `Imp.Canonical`, and the per-member textual encoders are open obligation #8
in `protocol/spec/v0.1.md`.
-/

namespace Imp

/-- Message id: 128-bit random value, unique per sender key (REQ-4.3). -/
abbrev MessageId := Nat

/--
Canonical envelope: one signed message (REQ-4.2, REQ-4.2, REQ-4.2,
REQ-4.4, REQ-4.5, REQ-4.2, REQ-4.8).

Parameterized by the signature scheme, so the signature type is the
scheme's: the protocol logic is agnostic to the concrete primitive.
-/
structure Envelope (S : SignatureScheme) where
  version    : Nat          -- `v` (REQ-4.2)
  sender     : String       -- `from` (REQ-4.2)
  recipients : List String  -- `to` (REQ-4.2)
  msgId      : MessageId    -- `msgid` (REQ-4.3)
  timestamp  : Nat          -- `ts`, Unix seconds (REQ-4.4)
  body       : List Nat     -- `payload` bytes (REQ-4.5)
  keyId      : Nat          -- `kid` (REQ-4.2)
  signature  : S.Signature  -- `sig` (REQ-4.8)

/--
The signed bytes: exactly the fields covered by the signature (REQ-4.7).
The `sig` field itself is not part of the signed bytes.
-/
def canonical {S : SignatureScheme} (e : Envelope S) : List Nat :=
  [e.version, e.msgId, e.timestamp, e.keyId] ++ e.body

/--
Field-level injectivity (REQ-4.9, SEC-2): two envelopes that agree on every
field are the same envelope. The byte-framing result is `Imp.body_injective` /
`Imp.signatureInput_injective` (`Imp.Canonical`); the per-member textual
encoders are open obligation #8 in `protocol/spec/v0.1.md`.
-/
theorem envelope_eq_of_fields {S : SignatureScheme} {e e' : Envelope S}
    (h1 : e.version = e'.version) (h2 : e.sender = e'.sender)
    (h3 : e.recipients = e'.recipients) (h4 : e.msgId = e'.msgId)
    (h5 : e.timestamp = e'.timestamp) (h6 : e.body = e'.body)
    (h7 : e.keyId = e'.keyId) (h8 : e.signature = e'.signature) : e = e' := by
  cases e <;> cases e' <;> simp_all

end Imp
