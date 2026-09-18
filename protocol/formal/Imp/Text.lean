import Imp.Canonical

/-!
# Imp.Text

Per-member textual encoders — part of REQ-4.9 / `[SEC-2]` (obligation #8).

`protocol/spec/v0.1.md` REQ-4.7 fixes how each member of an envelope is turned
into canonical bytes. `Imp.Canonical` proves the *framing* is injective; this
module proves injectivity of two of the textual encoders:

* `encNat` — minimal decimal integers (no leading zeros), used by `v` and `ts`.
  `encNat_injective` proves the encoding is injective, via the digit round trip
  `valOf_decDigits`.
* `encStr` — JSON string bodies with `"` and `\` escaped, wrapped in quotes,
  used by `from`, `msgid`, `type`, `payload`, `kid` and `sig`.
  `encStr_injective` proves the encoding is injective, via the un-escaper
  round trip `unesc_esc`.

**Scope note.** Base64 (the binary members) is proved in `Imp.Base64`. The
v0.1 `to` array framing is proved here (`encArray1_injective`) for the
single-recipient case REQ-4.2 mandates — with one element there are no
separator bytes, so the framing is a constant prefix and suffix around one
quoted string. A future multi-recipient version would need a separator-aware
encoder, since commas inside quoted strings require quote/escape tracking.
Also, `esc` handles only `"` and `\`; control characters (which JSON would
escape as `\u00XX`) are out of its scope, so callers must supply strings
without control bytes — the members this encoder serves (base64, addresses,
type names) all satisfy that.
-/

namespace Imp

/-! ## Minimal decimal integers -/

/--
Decimal digits of `n`, most significant first, with no leading zero; `[0]`
for zero.
-/
def decDigits (n : Nat) : List Nat :=
  if _h : n < 10 then [n] else decDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < 10) (Nat.not_lt.mp _h))
    (by decide : 1 < 10)

/-- Value of a digit list, most significant first. -/
def valOfAux (acc : Nat) : List Nat → Nat
  | [] => acc
  | d :: ds => valOfAux (acc * 10 + d) ds

def valOf (ds : List Nat) : Nat := valOfAux 0 ds

theorem valOfAux_append_single (acc : Nat) (ds : List Nat) (d : Nat) :
    valOfAux acc (ds ++ [d]) = valOfAux acc ds * 10 + d := by
  induction ds generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [valOfAux, ih]

/-- The digit list evaluates back to its number. -/
theorem valOf_decDigits (n : Nat) : valOf (decDigits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold decDigits
      split
      · simp [valOf, valOfAux]
      · rename_i h
        rw [valOf, valOfAux_append_single, ← valOf]
        rw [ih (n / 10)
          (Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < 10) (Nat.not_lt.mp h))
            (by decide : 1 < 10))]
        rw [Nat.mul_comm]
        exact Nat.div_add_mod n 10

/-- Decimal digit lists are injective. -/
theorem decDigits_injective {n m : Nat} (h : decDigits n = decDigits m) : n = m := by
  have := congrArg valOf h
  simpa [valOf_decDigits] using this

/-- Canonical decimal encoding: the ASCII digits of `n` (REQ-4.7). -/
def encNat (n : Nat) : Bytes := (decDigits n).map (fun d => d + 48)

/-- Strip the ASCII offset back to digits. -/
def digitsOfBytes (bs : Bytes) : List Nat := bs.map (fun b => b - 48)

theorem map_sub_add (ds : List Nat) :
    (ds.map (fun d => d + 48)).map (fun b => b - 48) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih, Nat.add_sub_cancel]

theorem digitsOfBytes_encNat (n : Nat) : digitsOfBytes (encNat n) = decDigits n := by
  simp only [digitsOfBytes, encNat]
  exact map_sub_add (decDigits n)

/-- Minimal decimal integers are injectively encoded (`v`, `ts`). -/
theorem encNat_injective {n m : Nat} (h : encNat n = encNat m) : n = m :=
  decDigits_injective (by
    have := congrArg digitsOfBytes h
    simpa [digitsOfBytes_encNat] using this)

/-! ## JSON string escaping -/

/-- Escape one byte: `"` → `\"`, `\` → `\\`, everything else unchanged. -/
def escByte (b : Nat) : Bytes :=
  if b = 34 then [92, 34] else if b = 92 then [92, 92] else [b]

/-- Escape every byte of a string body. -/
def esc : Bytes → Bytes
  | [] => []
  | b :: bs => escByte b ++ esc bs

/-- Inverse of `esc`. -/
def unesc : Bytes → Option Bytes
  | [] => some []
  | 92 :: b :: rest =>
      if b = 34 then (unesc rest).map (List.cons 34)
      else if b = 92 then (unesc rest).map (List.cons 92)
      else none
  | b :: rest => (unesc rest).map (List.cons b)

/-- Un-escaping recovers the original string body. -/
theorem unesc_esc (bs : Bytes) : unesc (esc bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      by_cases h34 : b = 34
      · simp [esc, escByte, unesc, ih, h34]
      · by_cases h92 : b = 92
        · simp [esc, escByte, unesc, ih, h34, h92]
        · simp [esc, escByte, unesc, ih, h34, h92]

/-- Escaping is injective. -/
theorem esc_injective {bs cs : Bytes} (h : esc bs = esc cs) : bs = cs := by
  have := congrArg unesc h
  simpa [unesc_esc] using this

/-- A canonical JSON string: quotes around the escaped body (REQ-4.7). -/
def encStr (bs : Bytes) : Bytes := 34 :: esc bs ++ [34]

/-- Cancelling a common one-element suffix, proved without quotient axioms. -/
theorem append_single_cancel {as cs : List Nat} {x : Nat}
    (h : as ++ [x] = cs ++ [x]) : as = cs := by
  induction as generalizing cs with
  | nil =>
      cases cs with
      | nil => rfl
      | cons c cs' => simp at h
  | cons a as ih =>
      cases cs with
      | nil => simp at h
      | cons c cs' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨hac, htail⟩ := h
          rw [hac, ih htail]

/-- Quoted escaped strings are injectively encoded (the string members). -/
theorem encStr_injective {bs cs : Bytes} (h : encStr bs = encStr cs) : bs = cs := by
  simp only [encStr] at h
  injection h with _ h'
  exact esc_injective (append_single_cancel h')


/-! ## v0.1 array framing -/

/-- The v0.1 `to` framing: exactly one element (REQ-4.2), so there are no
separator bytes — `[` then the single quoted string, then `]`. -/
def encArray1 (bs : Bytes) : Bytes := 91 :: encStr bs ++ [93]

/-- The v0.1 array framing is injective. (A future multi-recipient version
would need a separator-aware encoder: commas inside quoted strings make the
comma-joined form require quote/escape tracking.) -/
theorem encArray1_injective {bs cs : Bytes} (h : encArray1 bs = encArray1 cs) : bs = cs := by
  unfold encArray1 at h
  injection h with _ h'
  exact encStr_injective (append_single_cancel h')

end Imp
