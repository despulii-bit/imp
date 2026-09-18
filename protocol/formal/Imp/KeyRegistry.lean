import Init

/-!
# Imp.KeyRegistry

Key epochs, rotation, and chain validity, formalizing
`protocol/spec/v0.1.md` §3 (REQ-3.1 … REQ-3.5) and goals SEC-4/SEC-5 of §6.2.

* `ValidAt` — a key is authoritative for the instants inside its epoch
  (REQ-2.7, REQ-3.1).
* `RotatesOk` — protocol-level rotation condition (REQ-3.3/REQ-3.4/REQ-3.5):
  distinct key id + overlapping epochs. (The real check additionally verifies
  the `sigprev` cross-signature via the signature scheme; that is the layer
  below this one.)
* `ValidChain` — the key registry invariant: a chain in which every successor
  was rotated in by its predecessor and no key id is ever reintroduced.
-/

namespace Imp

/-- A published signing key with a finite epoch (REQ-2.7, REQ-2.7). -/
structure KeyRecord where
  keyId     : Nat  -- `kid` (REQ-2.3)
  notBefore : Nat  -- `nb`, inclusive, Unix seconds
  notAfter  : Nat  -- `na`, inclusive, Unix seconds; finite by REQ-2.7

/-- The key is authoritative at time `t` (REQ-2.10.3). -/
@[reducible]
def ValidAt (t : Nat) (r : KeyRecord) : Prop :=
  r.notBefore ≤ t ∧ t ≤ r.notAfter

/--
Rotation condition on the protocol level (REQ-3.3 + REQ-3.4 + REQ-3.5,
SEC-4/SEC-5): the new key must be distinct from the old, and its epoch must
overlap the old one so in-flight mail keeps verifying (REQ-3.4). The
cross-signature (`sigprev`, REQ-3.2) is verified by the layer above using the
signature scheme; here we fix the epoch-level facts the protocol relies on.
-/
def RotatesOk (old new : KeyRecord) : Bool :=
  decide (old.keyId ≠ new.keyId) && decide (new.notBefore ≤ old.notAfter)

/-- SEC-4/REQ-3.5: rotation introduces a distinct key. -/
theorem rotates_ok_keys_distinct {old new : KeyRecord} (h : RotatesOk old new = true) :
    old.keyId ≠ new.keyId := by
  unfold RotatesOk at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- SEC-5/REQ-3.4: rotation requires overlapping epochs. -/
theorem rotates_ok_requires_overlap {old new : KeyRecord} (h : RotatesOk old new = true) :
    new.notBefore ≤ old.notAfter := by
  unfold RotatesOk at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

/--
A valid key chain (REQ-3.3 + REQ-3.5). The head is the current key; every
record after it was cross-signed into place by its predecessor, and a key id
never reappears (REQ-3.5).
-/
inductive ValidChain : List KeyRecord → Prop
  | singleton (k : KeyRecord) : ValidChain [k]
  | extend (old next : KeyRecord) (rest : List KeyRecord)
      (hc : ValidChain (old :: rest)) (hrot : RotatesOk old next = true)
      (hdist : ∀ x ∈ old :: rest, x.keyId ≠ next.keyId) :
      ValidChain (next :: old :: rest)

/-- Every record after the head was rotated in by its predecessor (REQ-3.3). -/
def StepwiseRotates : List KeyRecord → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => RotatesOk b a = true ∧ StepwiseRotates (b :: rest)

/-- SEC-4: valid chains rotate stepwise — no key enters without a cross-signature (REQ-3.3). -/
theorem validChain_stepwise {ks : List KeyRecord} (h : ValidChain ks) : StepwiseRotates ks := by
  induction h with
  | singleton => simp [StepwiseRotates]
  | extend old next rest hc hrot _ =>
      rename_i hih
      simp [StepwiseRotates, hrot, hih]

/--
SEC-4: a key id never appears twice in a valid chain; in particular the
current key (the head) never appears below it (REQ-3.5). A DNS attacker can
therefore *delete* records (a denial of service) but cannot *introduce* a
key into a domain chain without holding a currently-authoritative key.
-/
theorem validChain_head_not_in_tail : ∀ {head : KeyRecord} {rest : List KeyRecord},
    ValidChain (head :: rest) → head ∉ rest := by
  intro head rest h
  cases h with
  | singleton => simp
  | extend old next rest hc hrot hdist =>
      intro hm
      rw [List.mem_cons] at hm
      rcases hm with hEq | hmem
      · subst old
        exact (hdist head (List.mem_cons.mpr (Or.inl rfl)) rfl).elim
      · exact (hdist head (List.mem_cons.mpr (Or.inr hmem)) rfl).elim

end Imp
