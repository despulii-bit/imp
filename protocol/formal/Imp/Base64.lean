import Imp.Canonical

/-!
# Imp.Base64

The **bit-packing core** of base64 — part of REQ-4.9 / `[SEC-2]` (obligation #8b).

Base64 turns three bytes into four six-bit *sextets*. This module proves that
this packing loses no information for byte-valued inputs (every byte < 256):
`byte0_sextet0`, `byte1_sextet1`, and `byte2_sextet2` show that the three
bytes are recovered exactly from the four sextets, and the range lemmas show
every sextet is a valid six-bit value (`< 64`).

That is the part of base64 where an error would be a real specification bug —
a bit-shift that dropped or duplicated bits would let two different payloads
share one canonical encoding, which is exactly what SEC-2 forbids.

The RFC 4648 alphabet (`b64char`/`b64val`, proved a bijection on the 64
sextets and never producing `=`), the `=` padding rules for one- and two-byte
tails, and the assembly over a whole byte list are proved as well:
`decB64_encB64` inverts the padded encoding, so `encB64_injective` holds for
byte-valued inputs. Obligation #8b is therefore closed for base64; the v0.1
`to` array framing is proved in `Imp.Text` (`encArray1_injective`).
-/

namespace Imp

/-! ## Sextet extraction

Input bytes are modelled as `Nat` with the byte precondition `b < 256`. -/

/-- Sextet 0: the top six bits of `b0`. -/
def sextet0 (b0 : Nat) : Nat := b0 / 4
/-- Sextet 1: the low two bits of `b0` and the top four bits of `b1`. -/
def sextet1 (b0 b1 : Nat) : Nat := (b0 % 4) * 16 + b1 / 16
/-- Sextet 2: the low four bits of `b1` and the top two bits of `b2`. -/
def sextet2 (b1 b2 : Nat) : Nat := (b1 % 16) * 4 + b2 / 64
/-- Sextet 3: the low six bits of `b2`. -/
def sextet3 (b2 : Nat) : Nat := b2 % 64

/-! ## Byte recovery -/

/-- Recover `b0` from sextets 0 and 1. -/
def byte0 (s0 s1 : Nat) : Nat := s0 * 4 + s1 / 16
/-- Recover `b1` from sextets 1 and 2. -/
def byte1 (s1 s2 : Nat) : Nat := (s1 % 16) * 16 + s2 / 4
/-- Recover `b2` from sextets 2 and 3. -/
def byte2 (s2 s3 : Nat) : Nat := (s2 % 4) * 64 + s3

/-! ## Arithmetic helpers -/

theorem div_sextet1 (b0 b1 : Nat) :
    sextet1 b0 b1 / 16 = b0 % 4 + b1 / 16 / 16 := by
  unfold sextet1
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 16), Nat.add_comm]

theorem div_sextet2 (b1 b2 : Nat) :
    sextet2 b1 b2 / 4 = b1 % 16 + b2 / 64 / 4 := by
  unfold sextet2
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 4), Nat.add_comm]

theorem mod_sextet1 (b0 b1 : Nat) : sextet1 b0 b1 % 16 = b1 / 16 % 16 := by
  unfold sextet1
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]

theorem mod_sextet2 (b1 b2 : Nat) : sextet2 b1 b2 % 4 = b2 / 64 % 4 := by
  unfold sextet2
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]

/-! ## The packing is invertible -/

/-- `b0` is recovered exactly from sextets 0 and 1. -/
theorem byte0_sextet0 {b0 b1 : Nat} (hb1 : b1 < 256) :
    byte0 (sextet0 b0) (sextet1 b0 b1) = b0 := by
  have hlt : b1 / 16 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr (by simpa using hb1)
  unfold byte0 sextet0
  rw [div_sextet1, Nat.div_eq_of_lt hlt, Nat.add_zero, Nat.mul_comm]
  exact Nat.div_add_mod b0 4

/-- `b1` is recovered exactly from sextets 1 and 2. -/
theorem byte1_sextet1 {b0 b1 b2 : Nat} (hb1 : b1 < 256) (hb2 : b2 < 256) :
    byte1 (sextet1 b0 b1) (sextet2 b1 b2) = b1 := by
  have hlt16 : b1 / 16 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr (by simpa using hb1)
  have hlt4 : b2 / 64 < 4 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr (by simpa using hb2)
  unfold byte1
  rw [mod_sextet1, Nat.mod_eq_of_lt hlt16, div_sextet2, Nat.div_eq_of_lt hlt4, Nat.add_zero,
    Nat.mul_comm]
  exact Nat.div_add_mod b1 16

/-- `b2` is recovered exactly from sextets 2 and 3. -/
theorem byte2_sextet2 {b1 b2 : Nat} (hb2 : b2 < 256) :
    byte2 (sextet2 b1 b2) (sextet3 b2) = b2 := by
  have hlt4 : b2 / 64 < 4 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr (by simpa using hb2)
  unfold byte2 sextet3
  rw [mod_sextet2, Nat.mod_eq_of_lt hlt4, Nat.mul_comm]
  exact Nat.div_add_mod b2 64

/-! ## Sextets are six-bit values -/

theorem sextet0_lt {b0 : Nat} (h : b0 < 256) : sextet0 b0 < 64 :=
  (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by simpa using h)

theorem sextet1_lt {b0 b1 : Nat} (h : b1 < 256) : sextet1 b0 b1 < 64 := by
  have hlt16 : b1 / 16 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr (by simpa using h)
  have h1 : (b0 % 4) * 16 ≤ 48 := by
    simpa using
      Nat.mul_le_mul_right 16 (Nat.le_of_lt_succ (Nat.mod_lt b0 (by decide : 0 < 4)))
  have h2 : b1 / 16 ≤ 15 := Nat.le_of_lt_succ hlt16
  unfold sextet1
  exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide : 48 + 15 < 64)

theorem sextet2_lt {b1 b2 : Nat} (h : b2 < 256) : sextet2 b1 b2 < 64 := by
  have hlt4 : b2 / 64 < 4 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr (by simpa using h)
  have h1 : (b1 % 16) * 4 ≤ 60 := by
    simpa using
      Nat.mul_le_mul_right 4 (Nat.le_of_lt_succ (Nat.mod_lt b1 (by decide : 0 < 16)))
  have h2 : b2 / 64 ≤ 3 := Nat.le_of_lt_succ hlt4
  unfold sextet2
  exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide : 60 + 3 < 64)

theorem sextet3_lt (b2 : Nat) : sextet3 b2 < 64 := Nat.mod_lt b2 (by decide : 0 < 64)

end Imp

namespace Imp

/-! ## The RFC 4648 alphabet -/

/-- RFC 4648 alphabet: sextet → ASCII code (`A–Z`, `a–z`, `0–9`, `+`, `/`). -/
def b64char (s : Nat) : Nat :=
  if s < 26 then 65 + s
  else if s < 52 then 97 + (s - 26)
  else if s < 62 then 48 + (s - 52)
  else if s = 62 then 43
  else 47

/-- Inverse: ASCII code → sextet. -/
def b64val (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 97 ≤ c ∧ c ≤ 122 then some (c - 97 + 26)
  else if 48 ≤ c ∧ c ≤ 57 then some (c - 48 + 52)
  else if c = 43 then some 62
  else if c = 47 then some 63
  else none

/-- The alphabet is inverted by `b64val` on all 64 sextets (checked by `decide`). -/
theorem b64_round_all :
    (List.range 64).all (fun s => decide (b64val (b64char s) = some s)) = true := by
  decide

/-- Every sextet round-trips through the alphabet. -/
theorem b64val_b64char {s : Nat} (hs : s < 64) : b64val (b64char s) = some s :=
  of_decide_eq_true (List.all_eq_true.mp b64_round_all s (List.mem_range.mpr hs))

/-- No alphabet character is `=` (61), so padding is unambiguous. -/
theorem b64_notpad_all :
    (List.range 64).all (fun s => decide (b64char s ≠ 61)) = true := by
  decide

theorem b64char_ne_pad {s : Nat} (hs : s < 64) : b64char s ≠ 61 :=
  of_decide_eq_true (List.all_eq_true.mp b64_notpad_all s (List.mem_range.mpr hs))

/-! ## Padded assembly -/

/-- Every element is a byte value. -/
def AllBytes (bs : Bytes) : Prop := ∀ b ∈ bs, b < 256

/-- A full three-byte group. -/
def encGroup (b0 b1 b2 : Nat) : Bytes :=
  [b64char (sextet0 b0), b64char (sextet1 b0 b1), b64char (sextet2 b1 b2),
   b64char (sextet3 b2)]

/-- A one-byte tail: two characters and `==`. -/
def encTail1 (b0 : Nat) : Bytes :=
  [b64char (sextet0 b0), b64char (sextet1 b0 0), 61, 61]

/-- A two-byte tail: three characters and `=`. -/
def encTail2 (b0 b1 : Nat) : Bytes :=
  [b64char (sextet0 b0), b64char (sextet1 b0 b1), b64char (sextet2 b1 0), 61]

/-- Standard base64 with padding (REQ-4.7). -/
def encB64 : Bytes → Bytes
  | [] => []
  | [b0] => encTail1 b0
  | [b0, b1] => encTail2 b0 b1
  | b0 :: b1 :: b2 :: rest => encGroup b0 b1 b2 ++ encB64 rest

/-- Inverse of `encB64`: read a group, dispatch on the padding, recurse. -/
def decB64 : Bytes → Option Bytes
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
      if c3 = 61 then
        if c2 = 61 then
          match b64val c0, b64val c1 with
          | some s0, some s1 => (decB64 rest).map (List.cons (byte0 s0 s1))
          | _, _ => none
        else
          match b64val c0, b64val c1, b64val c2 with
          | some s0, some s1, some s2 =>
              (decB64 rest).map (fun t => byte0 s0 s1 :: byte1 s1 s2 :: t)
          | _, _, _ => none
      else
        match b64val c0, b64val c1, b64val c2, b64val c3 with
        | some s0, some s1, some s2, some s3 =>
            (decB64 rest).map (fun t => byte0 s0 s1 :: byte1 s1 s2 :: byte2 s2 s3 :: t)
        | _, _, _, _ => none
  | _ => none

theorem decB64_encB64_aux : ∀ n : Nat, ∀ bs : Bytes, bs.length = n → AllBytes bs →
    decB64 (encB64 bs) = some bs := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro bs hlen hb
      match bs with
      | [] => rfl
      | [b0] =>
          have h0 : b0 < 256 := hb b0 (by simp)
          simp [encB64, encTail1, decB64,
            b64val_b64char (sextet0_lt h0),
            b64val_b64char (sextet1_lt (b0 := b0) (b1 := 0) (by decide : (0 : Nat) < 256)),
            byte0_sextet0 (b0 := b0) (b1 := 0) (by decide : (0 : Nat) < 256)]
      | [b0, b1] =>
          have h0 : b0 < 256 := hb b0 (by simp)
          have h1 : b1 < 256 := hb b1 (by simp)
          simp [encB64, encTail2, decB64,
            b64val_b64char (sextet0_lt h0),
            b64val_b64char (sextet1_lt (b0 := b0) (b1 := b1) h1),
            b64val_b64char (sextet2_lt (b1 := b1) (b2 := 0) (by decide : (0 : Nat) < 256)),
            b64char_ne_pad (sextet2_lt (b1 := b1) (b2 := 0) (by decide : (0 : Nat) < 256)),
            byte0_sextet0 (b0 := b0) (b1 := b1) h1,
            byte1_sextet1 (b0 := b0) (b1 := b1) (b2 := 0) h1 (by decide : (0 : Nat) < 256)]
      | b0 :: b1 :: b2 :: rest =>
          have h0 : b0 < 256 := hb b0 (by simp)
          have h1 : b1 < 256 := hb b1 (by simp)
          have h2 : b2 < 256 := hb b2 (by simp)
          have hrest : AllBytes rest := fun x hx => hb x (by simp [hx])
          have hlt : rest.length < n := by
            rw [← hlen]
            simp only [List.length_cons]
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rest.length) (by simp)
          have ih' := ih rest.length hlt rest rfl hrest
          simp only [encB64, encGroup, List.cons_append, List.nil_append]
          rw [decB64]
          rw [if_neg (b64char_ne_pad (sextet3_lt b2))]
          simp [b64val_b64char (sextet0_lt h0),
            b64val_b64char (sextet1_lt (b0 := b0) (b1 := b1) h1),
            b64val_b64char (sextet2_lt (b1 := b1) (b2 := b2) h2),
            b64val_b64char (sextet3_lt b2), ih',
            byte0_sextet0 (b0 := b0) (b1 := b1) h1,
            byte1_sextet1 (b0 := b0) (b1 := b1) (b2 := b2) h1 h2,
            byte2_sextet2 (b1 := b1) (b2 := b2) h2]

/-- The padded encoding is inverted by `decB64` on byte inputs. -/
theorem decB64_encB64 (bs : Bytes) (hb : AllBytes bs) : decB64 (encB64 bs) = some bs :=
  decB64_encB64_aux bs.length bs rfl hb

/-- Base64 with padding is injective on byte inputs (REQ-4.9). -/
theorem encB64_injective {bs cs : Bytes} (hb : AllBytes bs) (hc : AllBytes cs)
    (h : encB64 bs = encB64 cs) : bs = cs := by
  have h' := congrArg decB64 h
  rw [decB64_encB64 bs hb, decB64_encB64 cs hc] at h'
  simpa using h'

end Imp
