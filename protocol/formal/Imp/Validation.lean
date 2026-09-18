import Imp.Envelope
import Imp.KeyRegistry

/-!
# Imp.Validation

The receiver acceptance gate (REQ-6.1, `protocol/spec/v0.1.md` §6) and the
machine-checked security claims SEC-1 and SEC-3 (§6.2).

* `validate` — the gate: signature verifies under the sender's key (REQ-6.1.4),
  key epoch covers `ts` (REQ-2.10.3), `msgid` was not processed before
  (REQ-6.1.6, REQ-6.1.6).
* `acceptOnce` — atomic accept: on success the `msgid` is durably marked.
* `processAll` — batch processing preserving the processed-id set.
-/

namespace Imp

/-- Mark message id `id` as processed, keeping all previously processed ids. -/
def markSeen (seen : Nat → Bool) (id : Nat) : Nat → Bool :=
  fun i => if i = id then true else seen i

/--
The validation gate (REQ-6.1, REQ-6.1.5/REQ-6.1.6, SEC-1/SEC-3).
`pub` is the sender-domain public key bound to `rec.keyId` by the sender's
DNS (REQ-2.10); `seen` is the set of processed message ids.
-/
def validate {S : SignatureScheme} (pub : S.PublicKey) (rec : KeyRecord) (seen : Nat → Bool)
    (env : Envelope S) : Bool :=
  S.verify pub (canonical env) env.signature &&
    decide (ValidAt env.timestamp rec) && !seen env.msgId

/--
Atomic accept (REQ-6.1): if validation passes, the message id is durably
marked; otherwise `none` and nothing is marked.
-/
def acceptOnce {S : SignatureScheme} (pub : S.PublicKey) (rec : KeyRecord) (seen : Nat → Bool)
    (env : Envelope S) : Option (Nat → Bool) :=
  if validate pub rec seen env = true then some (markSeen seen env.msgId) else none

/-! ## SEC-1 — sender authentication -/

/-- SEC-1a: acceptance requires the signature to verify under the sender's key (REQ-6.1.4). -/
theorem validate_ok_implies_sig {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S}
    (h : validate pub rec seen env = true) :
    S.verify pub (canonical env) env.signature = true := by
  unfold validate at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- SEC-1b: acceptance requires the sender's key epoch to cover `ts` (REQ-2.10.3). -/
theorem validate_ok_implies_valid_at {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S}
    (h : validate pub rec seen env = true) : ValidAt env.timestamp rec := by
  unfold validate at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-! ## SEC-3 — replay resistance -/

/-- `!b = true` iff `b = false` (computational, no axioms). -/
theorem bool_not_eq_true_iff (b : Bool) : (!b = true) ↔ b = false := by
  cases b <;> simp

/-- SEC-3a: acceptance requires the `msgid` to be unseen (REQ-6.1.6, REQ-6.1.6). -/
theorem validate_ok_implies_unseen {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S}
    (h : validate pub rec seen env = true) : seen env.msgId = false := by
  unfold validate at h
  exact (bool_not_eq_true_iff (seen env.msgId)).mp
    (by simpa using (Bool.and_eq_true_iff.mp h).2)

/-- SEC-3b: a successful accept marks the `msgid` as processed. -/
theorem accept_once_marks_id {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S} {seen' : Nat → Bool}
    (h : acceptOnce pub rec seen env = some seen') : seen' env.msgId = true := by
  unfold acceptOnce at h
  by_cases hv : validate pub rec seen env = true
  · simp [hv] at h
    subst seen'
    simp [markSeen]
  · simp [hv] at h

/-- SEC-3c: re-accepting the same `msgid` is refused (REQ-6.1.6 → 409). -/
theorem accept_once_blocks_duplicate {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S} {seen' : Nat → Bool}
    (h : acceptOnce pub rec seen env = some seen') : acceptOnce pub rec seen' env = none := by
  unfold acceptOnce at h ⊢
  by_cases hv : validate pub rec seen env = true
  · simp [hv] at h
    subst seen'
    have hv' : validate pub rec (markSeen seen env.msgId) env = false := by
      unfold validate
      simp [markSeen]
    simp [hv']
  · simp [hv] at h

/-- SEC-3d: accepting never un-marks previously processed ids. -/
theorem accept_once_keeps_old {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S} {seen' : Nat → Bool}
    (h : acceptOnce pub rec seen env = some seen') :
    ∀ id : Nat, seen id = true → seen' id = true := by
  unfold acceptOnce at h
  by_cases hv : validate pub rec seen env = true
  · simp [hv] at h
    subst seen'
    intro id hid
    by_cases heq : id = env.msgId
    · simp [heq, markSeen]
    · simp [heq, markSeen, hid]
  · simp [hv] at h

/-- Batch delivery: process one message at a time, stopping at the first rejection. -/
def processAll {S : SignatureScheme} (pub : S.PublicKey) (rec : KeyRecord) (seen : Nat → Bool) :
    List (Envelope S) → Option (Nat → Bool)
  | [] => some seen
  | e :: es =>
      match acceptOnce pub rec seen e with
      | none => none
      | some seen' => processAll pub rec seen' es

/-- SEC-3e: batch processing preserves every previously processed id. -/
theorem processAll_keeps_old {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord} :
    ∀ (seen : Nat → Bool) (es : List (Envelope S)) (seen' : Nat → Bool),
      processAll pub rec seen es = some seen' → ∀ id : Nat, seen id = true → seen' id = true := by
  intro seen es
  induction es generalizing seen with
  | nil =>
      intro seen' h id hid
      simp [processAll] at h
      subst seen'
      exact hid
  | cons e es ih =>
      intro seen' h id hid
      unfold processAll at h
      cases hEq : acceptOnce pub rec seen e with
      | none => simp [hEq] at h
      | some seen0 =>
          simp [hEq] at h
          exact ih seen0 seen' h id (accept_once_keeps_old hEq id hid)

/-! ## Headline claim -/

/--
SEC-1 + SEC-3 combined: a message that is accepted was authenticated
(signature verified under the sender key whose epoch covers `ts`) and was
fresh (its id had not been processed before). This is the property that
replaces email's reputation model: acceptance is a function of cryptographic
identity and freshness, not of history (REQ-1.1).
-/
theorem accept_implies_security {S : SignatureScheme} {pub : S.PublicKey} {rec : KeyRecord}
    {seen : Nat → Bool} {env : Envelope S} {seen' : Nat → Bool}
    (h : acceptOnce pub rec seen env = some seen') :
    S.verify pub (canonical env) env.signature = true ∧
      ValidAt env.timestamp rec ∧ seen env.msgId = false := by
  unfold acceptOnce at h
  by_cases hv : validate pub rec seen env = true
  · have hv' := hv
    simp [hv] at h
    constructor
    · exact validate_ok_implies_sig hv'
    · constructor
      · exact validate_ok_implies_valid_at hv'
      · exact validate_ok_implies_unseen hv'
  · simp [hv] at h

end Imp
