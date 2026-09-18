import Init

/-!
# Imp.Signature

Abstract signature primitive (Ed25519 in practice; see
`protocol/spec/v0.1.md` REQ-2.3 for the algorithm and REQ-4.10 for the
correctness assumption).

Cryptanalytic soundness of the concrete primitive is a *trusted assumption*:
the protocol logic formalized in this repository is parametric over this
interface, relying on exactly one property — signature correctness
(`sign_verify`). Everything proved downstream is machine-checked on top of it.
-/

namespace Imp

/--
An abstract signature scheme with the one property the protocol needs:
a signature produced with a secret key verifies under the corresponding
public key (`pubOf`). See `protocol/spec/v0.1.md` §6.4,
"Assumption boundary".
-/
structure SignatureScheme where
  PublicKey : Type
  SecretKey : Type
  Signature : Type
  pubOf     : SecretKey → PublicKey
  sign      : SecretKey → List Nat → Signature
  verify    : PublicKey → List Nat → Signature → Bool
  sign_verify : ∀ (sk : SecretKey) (m : List Nat),
    verify (pubOf sk) m (sign sk m) = true

end Imp
