import Init

/-!
# Imp.Canonical

Canonical byte framing for the IMP envelope — the structural half of
REQ-4.9 / `[SEC-2]`.

`protocol/spec/v0.1.md` REQ-4.7 says a canonical serialization writes the
envelope's members in lexicographic order, with no insignificant whitespace,
so that a signature can bind exactly one message. The structural question —
*do the bytes determine the members?* — is answered here:

* `encBlock` / `encBlocks` model a sequence of **self-delimiting blocks**:
  each block writes its own length, then its contents, so block boundaries are
  unambiguous without any separator byte.
* `encBlocks_injective` proves the framing determines its blocks.
* `Wire` models a message whose members are each in their canonical *textual*
  byte form (`Bytes`); `bodyBlocks` / `signatureInputBlocks` list the members
  in the canonical (sorted) order of REQ-4.7, with the fixed quoted member
  names interleaved as constant blocks.
* `body_injective` proves the canonical body determines the whole message
  (REQ-4.9), and `signatureInput_injective` proves the signed bytes determine
  exactly the signed members (SEC-2).

**What is proved, and what is not.** This module proves the *framing*:
ordering, block boundaries, the fixed member names, and that no member can be
confused with another. It does **not** prove the per-member *textual* encoders
— minimal decimal integers, JSON string escaping, standard base64, and the
array framing of `to` — injective. Those are standard, separately checkable
facts; their behaviour is pinned concretely by the conformance vectors in
`protocol/spec/conformance.md` (Annex B). They are tracked as open obligation
#8 in §9 of the contract, while obligation #1 (framing) is closed here.
-/

namespace Imp

/-- Bytes are modelled as natural numbers (0..255 by convention). -/
abbrev Bytes := List Nat

/-- A self-delimiting block: its length, then its contents. -/
def encBlock (b : Bytes) : Bytes := b.length :: b

/-- Concatenation of self-delimiting blocks. -/
def encBlocks : List Bytes → Bytes
  | [] => []
  | b :: bs => encBlock b ++ encBlocks bs

/--
The framing is unambiguous: the concatenation of self-delimiting blocks
determines the blocks. This is the core of REQ-4.9 — no separator byte is
needed, and no two different block sequences can produce the same bytes.
-/
theorem encBlocks_injective {bs : List Bytes} :
    ∀ {cs : List Bytes}, encBlocks bs = encBlocks cs → bs = cs := by
  induction bs with
  | nil =>
      intro cs h
      cases cs with
      | nil => rfl
      | cons c cs' => simp [encBlocks, encBlock] at h
  | cons b bs ih =>
      intro cs h
      cases cs with
      | nil => simp [encBlocks, encBlock] at h
      | cons c cs' =>
          simp only [encBlocks, encBlock, List.cons_append] at h
          injection h with hlen htail
          have hb : b = c := by
            calc b = (b ++ encBlocks bs).take b.length := List.take_left.symm
                 _ = (c ++ encBlocks cs').take b.length := by rw [htail]
                 _ = (c ++ encBlocks cs').take c.length := by rw [hlen]
                 _ = c := List.take_left
          have henc : encBlocks bs = encBlocks cs' := by
            have h' := htail
            rw [hb] at h'
            exact List.append_cancel_left h'
          rw [hb]
          exact congrArg (List.cons c) (ih henc)

/-! ## Member names (constant blocks) -/

/-- `"from"`, the ASCII bytes of the quoted JSON member name. -/
def nFrom    : Bytes := [34, 102, 114, 111, 109, 34]
/-- `"kid"`. -/
def nKid     : Bytes := [34, 107, 105, 100, 34]
/-- `"msgid"`. -/
def nMsgid   : Bytes := [34, 109, 115, 103, 105, 100, 34]
/-- `"payload"`. -/
def nPayload : Bytes := [34, 112, 97, 121, 108, 111, 97, 100, 34]
/-- `"sig"`. -/
def nSig     : Bytes := [34, 115, 105, 103, 34]
/-- `"to"`. -/
def nTo      : Bytes := [34, 116, 111, 34]
/-- `"ts"`. -/
def nTs      : Bytes := [34, 116, 115, 34]
/-- `"type"`. -/
def nType    : Bytes := [34, 116, 121, 112, 101, 34]
/-- `"v"`. -/
def nV       : Bytes := [34, 118, 34]

/-! ## The message model -/

/--
A message whose members are each already in their canonical textual byte form.
(`Bytes` here is the member's canonical encoding as a byte string; how a `Nat`
timestamp or a UTF-8 address becomes those bytes is the textual layer, see the
module note.)
-/
structure Wire where
  version    : Bytes
  sender     : Bytes
  recipients : Bytes
  msgId      : Bytes
  timestamp  : Bytes
  type       : Bytes
  payload    : Bytes
  keyId      : Bytes
  signature  : Bytes

/-- The signed projection of a message: all members except `signature`. -/
structure Signed where
  version    : Bytes
  sender     : Bytes
  recipients : Bytes
  msgId      : Bytes
  timestamp  : Bytes
  type       : Bytes
  payload    : Bytes
  keyId      : Bytes

/-- Project a message onto the members the signature covers. -/
def signedOf (w : Wire) : Signed :=
  { version := w.version, sender := w.sender, recipients := w.recipients,
    msgId := w.msgId, timestamp := w.timestamp, type := w.type,
    payload := w.payload, keyId := w.keyId }

/-- The signed members in canonical (sorted) order: the signature input. -/
def signatureInputBlocks (w : Wire) : List Bytes :=
  [nFrom, w.sender, nKid, w.keyId, nMsgid, w.msgId, nPayload, w.payload,
   nTo, w.recipients, nTs, w.timestamp, nType, w.type, nV, w.version]

/-- All members in canonical (sorted) order: the transmitted body. -/
def bodyBlocks (w : Wire) : List Bytes :=
  [nFrom, w.sender, nKid, w.keyId, nMsgid, w.msgId, nPayload, w.payload,
   nSig, w.signature, nTo, w.recipients, nTs, w.timestamp,
   nType, w.type, nV, w.version]

/-- The canonical signature input bytes (REQ-4.8). -/
def signatureInput (w : Wire) : Bytes := encBlocks (signatureInputBlocks w)

/-- The canonical body bytes (REQ-4.7, including `sig`). -/
def body (w : Wire) : Bytes := encBlocks (bodyBlocks w)

/--
REQ-4.9: the canonical body determines the entire message. Two messages with
the same canonical bytes are the same message — the signature binds exactly
one envelope.
-/
theorem body_injective {w w' : Wire} (h : body w = body w') : w = w' := by
  have hb : bodyBlocks w = bodyBlocks w' := encBlocks_injective h
  cases w; cases w'
  simp_all [bodyBlocks]

/--
SEC-2: the signed bytes determine exactly the signed members. Any change to a
signed member changes the signature input, so a signature cannot be moved to a
different message.
-/
theorem signatureInput_injective {w w' : Wire}
    (h : signatureInput w = signatureInput w') : signedOf w = signedOf w' := by
  have hb : signatureInputBlocks w = signatureInputBlocks w' := encBlocks_injective h
  cases w; cases w'
  simp_all [signatureInputBlocks, signedOf]

end Imp
