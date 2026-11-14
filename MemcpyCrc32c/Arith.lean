/-
CRC arithmetic with abseil's semantics: `ExtendCrc32cByZeroes`, `ConcatCrc32c`,
`RemoveCrc32cPrefix`, `RemoveCrc32cSuffix`, each proven against the spec.

abseil implements these with tables of `X^(2^k)` powers; here the same
multiplications modulo `G` are done by square-and-multiply, which is
O(log n) word operations. Table-driven variants for the hot path come later
and will be proven equal to these.
-/
import MemcpyCrc32c.Bitwise

namespace Crc32c
open Polynomial

/-! ### Multiplication and powers modulo `G` on reflected 32-bit words -/

/-- `acc + a * b` modulo `G`, consuming `n` coefficients of `b` from `X^0` up. -/
def mulMod.go : Nat → UInt32 → UInt32 → UInt32 → UInt32
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    mulMod.go n (stepBit a) (b <<< 1) (if b &&& 0x80000000 = 0x80000000 then acc ^^^ a else acc)

/-- Product modulo `G` of two reflected 32-bit polynomials. -/
def mulMod (a b : UInt32) : UInt32 := mulMod.go 32 a b 0

/-- `a ^ n` modulo `G`, by square-and-multiply: O(log n) multiplications. -/
def powMod (a : UInt32) (n : Nat) : UInt32 :=
  if n = 0 then 0x80000000
  else
    let h := powMod a (n / 2)
    let sq := mulMod h h
    if n % 2 = 1 then mulMod sq a else sq
termination_by n
decreasing_by omega

/-- `X^8`, reflected. -/
def x8 : UInt32 := 0x00800000

/-- `X^(-8)` modulo `G`, reflected. Checked by `stepByte_xInv8`. -/
def xInv8 : UInt32 := 0xFDE39562

/-- Extend an unconditioned state over `n` zero bytes: multiply by `X^(8n)`. -/
def extendZeroesRaw (s : UInt32) (n : Nat) : UInt32 := mulMod s (powMod x8 n)

/-- Inverse of `extendZeroesRaw`: multiply by `X^(-8n)`. -/
def unextendZeroesRaw (s : UInt32) (n : Nat) : UInt32 := mulMod s (powMod xInv8 n)

/-- `absl::ExtendCrc32cByZeroes`. -/
def extendZeroes (c : UInt32) (n : Nat) : UInt32 :=
  extendZeroesRaw (c ^^^ 0xFFFFFFFF) n ^^^ 0xFFFFFFFF

/-- `absl::ConcatCrc32c`. -/
def concat (lhsCrc rhsCrc : UInt32) (rhsLen : Nat) : UInt32 :=
  extendZeroesRaw lhsCrc rhsLen ^^^ rhsCrc

/-- `absl::RemoveCrc32cPrefix`. -/
def removePrefix (crcA crcAB : UInt32) (lenB : Nat) : UInt32 := concat crcA crcAB lenB

/-- `absl::RemoveCrc32cSuffix`. -/
def removeSuffix (fullCrc suffixCrc : UInt32) (suffixLen : Nat) : UInt32 :=
  unextendZeroesRaw (fullCrc ^^^ suffixCrc) suffixLen

/-! ### Bridge lemmas -/

theorem P_zero : P 0 = 0 := polyR_zero

theorem eq_of_π_P {a b : UInt32} (h : π (P a) = π (P b)) : a = b :=
  P_injective (eq_of_π_eq (degree_P_lt a) (degree_P_lt b) h)

/-- Peel the constant term off the reflected view. -/
theorem polyR_eq_msb_add {w : Nat} (v : BitVec w) :
    polyR v = (if v.getLsbD (w - 1) then (1 : (ZMod 2)[X]) else 0) + X * polyR (v <<< 1) := by
  ext k
  rw [coeff_add, apply_ite (fun p : (ZMod 2)[X] => p.coeff k), coeff_one, coeff_zero]
  cases k with
  | zero =>
    simp only [coeff_X_mul_zero, coeff_polyR]
    by_cases hw : 0 < w
    · simp [hw]
    · have : w = 0 := by omega
      subst this; simp
  | succ k =>
    simp only [coeff_X_mul, coeff_polyR, BitVec.getLsbD_shiftLeft]
    by_cases hk : k + 1 < w
    · have h1 : k < w := by omega
      have h2 : w - 1 - k < w := by omega
      have h3 : ¬ w - 1 - k < 1 := by omega
      have h4 : w - 1 - k - 1 = w - 1 - (k + 1) := by omega
      simp [hk, h1, h2, h3, h4]
    · by_cases hk' : k < w
      · have h3 : w - 1 - k < 1 := by omega
        simp [hk, hk', h3]
      · simp [hk, hk']

theorem and_msb_eq_iff (s : UInt32) :
    s &&& 0x80000000 = 0x80000000 ↔ s.toBitVec.getLsbD 31 = true := by
  rw [← UInt32.toBitVec_inj]
  have e : (0x80000000 : UInt32).toBitVec = BitVec.twoPow 32 31 := rfl
  simp only [UInt32.toBitVec_and, e]
  constructor
  · intro h
    have := congrArg (fun v => v.getLsbD 31) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hi' : i = 31
    · subst hi'; simpa using h
    · simp [BitVec.getLsbD_twoPow, Ne.symm hi']

theorem π_P_mulMod_go (n : Nat) (a b acc : UInt32)
    (hb : ∀ i, i + n < 32 → b.toBitVec.getLsbD i = false) :
    π (P (mulMod.go n a b acc)) = π (P acc) + π (P a) * π (P b) := by
  induction n generalizing a b acc with
  | zero =>
    have : b = 0 := by
      rw [← UInt32.toBitVec_inj]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [hb i (by omega)]
    subst this
    rw [mulMod.go, P_zero]; simp
  | succ n ih =>
    have hs : (b <<< 1).toBitVec = b.toBitVec <<< 1 := by simp
    rw [mulMod.go, ih]
    · have hbP : P b = (if b.toBitVec.getLsbD 31 then (1 : (ZMod 2)[X]) else 0) + X * P (b <<< 1) := by
        have := polyR_eq_msb_add b.toBitVec
        simpa [P, hs] using this
      rw [π_P_stepBit, hbP]
      by_cases h : b.toBitVec.getLsbD 31 = true
      · have hc := (and_msb_eq_iff b).mpr h
        simp only [hc, h, ↓reduceIte, P_xor, map_add, map_mul, map_one]
        ring
      · have hc : ¬ (b &&& 0x80000000 = 0x80000000) := fun hc => h ((and_msb_eq_iff b).mp hc)
        simp only [hc, h, Bool.false_eq_true, ↓reduceIte, map_add, map_mul, map_zero]
        ring
    · intro i hi
      rw [hs, BitVec.getLsbD_shiftLeft]
      cases i with
      | zero => simp
      | succ i =>
        have := hb i (by omega)
        simp [this]

theorem π_P_mulMod (a b : UInt32) : π (P (mulMod a b)) = π (P a) * π (P b) := by
  rw [mulMod, π_P_mulMod_go 32 a b 0 (fun i hi => by omega), P_zero]
  simp

set_option maxRecDepth 100000 in
theorem P_one : P 0x80000000 = 1 := by
  simp +decide [P, polyR, ofBits, Finset.sum_range_succ, BitVec.getLsbD]

set_option maxRecDepth 100000 in
theorem P_x8 : P x8 = X ^ 8 := by
  have e : x8.toBitVec = 0x00800000#32 := rfl
  simp +decide [P, e, polyR, ofBits, Finset.sum_range_succ, BitVec.getLsbD]

theorem π_P_powMod (a : UInt32) (n : Nat) : π (P (powMod a n)) = π (P a) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [powMod]
    by_cases hn : n = 0
    · simp [hn, P_one]
    · have hlt : n / 2 < n := by omega
      simp only [hn, ↓reduceIte]
      by_cases hodd : n % 2 = 1
      · simp only [hodd, ↓reduceIte, π_P_mulMod, ih _ hlt]
        conv_rhs => rw [show n = n / 2 + n / 2 + 1 by omega]
        ring
      · simp only [hodd, ↓reduceIte, π_P_mulMod, ih _ hlt]
        conv_rhs => rw [show n = n / 2 + n / 2 by omega]
        ring

theorem stepByte_xInv8 : stepByte xInv8 0 = 0x80000000 := by decide

/-- `xInv8` really is the inverse of `X^8` modulo `G`. -/
theorem π_P_xInv8 : π (P xInv8) * π X ^ 8 = 1 := by
  have h := π_P_stepByte xInv8 0
  rw [stepByte_xInv8, P_one] at h
  have z : polyR (0 : UInt8).toBitVec = 0 := polyR_zero
  rw [z] at h
  simpa using h.symm

theorem π_P_extendZeroesRaw (s : UInt32) (n : Nat) :
    π (P (extendZeroesRaw s n)) = π (P s) * π X ^ (8 * n) := by
  rw [extendZeroesRaw, π_P_mulMod, π_P_powMod, P_x8, map_pow, pow_mul]

theorem π_P_unextendZeroesRaw (s : UInt32) (n : Nat) :
    π (P (unextendZeroesRaw s n)) * π X ^ (8 * n) = π (P s) := by
  rw [unextendZeroesRaw, π_P_mulMod, π_P_powMod, pow_mul, mul_assoc, ← mul_pow, π_P_xInv8]
  simp

/-- The all-ones conditioning word as a residue. -/
noncomputable abbrev F : Q := π (P 0xFFFFFFFF)

theorem π_P_extend (c : UInt32) (bs : ByteArray) :
    π (P (extend c bs)) =
      (π (P c) + F) * π X ^ (8 * bs.size) + π (msgPoly bs.data.toList) * π X ^ 32 + F := by
  simp [extend, P_xor, π_P_rawExtend]

theorem msgPoly_append (a b : List UInt8) :
    msgPoly (a ++ b) = msgPoly a * X ^ (8 * b.length) + msgPoly b := by
  induction a with
  | nil => simp [msgPoly]
  | cons x a ih =>
    simp only [List.cons_append, msgPoly, ih, List.length_append]
    ring

theorem msgPoly_replicate_zero (n : Nat) : msgPoly (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, msgPoly, ih]
    exact polyR_zero

/-! ### Theorems 1 to 5 of the brief -/

/-- Theorem 1. -/
theorem extend_append (c : UInt32) (a b : ByteArray) :
    extend (extend c a) b = extend c (a ++ b) := by
  simp [extend, rawExtend, UInt32.xor_assoc]

/-- Theorem 2: `ConcatCrc32c`. -/
theorem concat_spec (a b : ByteArray) :
    concat (crc32c a) (crc32c b) b.size = crc32c (a ++ b) := by
  apply eq_of_π_P
  simp only [concat, crc32c, P_xor, map_add, π_P_extendZeroesRaw, π_P_extend,
    ByteArray.size_append, ByteArray.data_append, Array.toList_append, msgPoly_append,
    map_mul, map_pow, Array.length_toList, ByteArray.size_data, P_zero, map_zero, zero_add]
  linear_combination Q_add_self (F * π X ^ (8 * b.size))

/-- Theorem 3: `RemoveCrc32cPrefix`. -/
theorem removePrefix_spec (a b : ByteArray) :
    removePrefix (crc32c a) (crc32c (a ++ b)) b.size = crc32c b := by
  apply eq_of_π_P
  simp only [removePrefix, concat, crc32c, P_xor, map_add, π_P_extendZeroesRaw, π_P_extend,
    ByteArray.size_append, ByteArray.data_append, Array.toList_append, msgPoly_append,
    map_mul, map_pow, Array.length_toList, ByteArray.size_data, P_zero, map_zero, zero_add]
  linear_combination Q_add_self (F * π X ^ (8 * a.size + 8 * b.size)) +
    Q_add_self (π (msgPoly a.data.toList) * π X ^ (8 * b.size) * π X ^ 32)

/-- Theorem 4: `RemoveCrc32cSuffix`. -/
theorem removeSuffix_spec (a b : ByteArray) :
    removeSuffix (crc32c (a ++ b)) (crc32c b) b.size = crc32c a := by
  apply eq_of_π_P
  have hu := π_P_unextendZeroesRaw (crc32c (a ++ b) ^^^ crc32c b) b.size
  have hinv : (π (P xInv8) ^ b.size) * π X ^ (8 * b.size) = 1 := by
    rw [pow_mul, ← mul_pow, π_P_xInv8, one_pow]
  have e : π (P (crc32c (a ++ b) ^^^ crc32c b)) = π (P (crc32c a)) * π X ^ (8 * b.size) := by
    simp only [crc32c, P_xor, map_add, π_P_extend,
      ByteArray.size_append, ByteArray.data_append, Array.toList_append, msgPoly_append,
      map_mul, map_pow, Array.length_toList, ByteArray.size_data, P_zero, map_zero, zero_add]
    linear_combination Q_add_self F +
      Q_add_self (π (msgPoly b.data.toList) * π X ^ 32)
  rw [removeSuffix, unextendZeroesRaw, π_P_mulMod, π_P_powMod, e]
  linear_combination π (P (crc32c a)) * hinv

/-- Theorem 5: `ExtendCrc32cByZeroes`. -/
theorem extendZeroes_spec (c : UInt32) (n : Nat) :
    extendZeroes c n = extend c (ByteArray.mk (Array.replicate n 0)) := by
  apply eq_of_π_P
  simp [extendZeroes, P_xor, π_P_extendZeroesRaw, π_P_extend, msgPoly_replicate_zero,
    ByteArray.size]

end Crc32c
