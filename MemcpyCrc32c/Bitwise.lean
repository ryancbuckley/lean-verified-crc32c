/-
The bitwise executable reference, proven equal to the polynomial spec.
-/
import MemcpyCrc32c.Spec
import MemcpyCrc32c.Impl.Reference

namespace Crc32c
open Polynomial

/-! ### Bridge lemmas: words to polynomials -/

/-- Reflected polynomial view of a 32-bit CRC state. -/
noncomputable abbrev P (s : UInt32) : (ZMod 2)[X] := polyR s.toBitVec

theorem degree_P_lt (s : UInt32) : (P s).degree < 32 := degree_polyR_lt _

theorem P_injective : Function.Injective P := fun _ _ h =>
  UInt32.toBitVec_inj.mp (polyR_injective h)

theorem P_xor (a b : UInt32) : P (a ^^^ b) = P a + P b := by
  simp [P, polyR_xor]

theorem and_one_eq_one_iff (s : UInt32) : s &&& 1 = 1 ↔ s.toBitVec.getLsbD 0 = true := by
  rw [← UInt32.toBitVec_inj]
  simp only [UInt32.toBitVec_and]
  constructor
  · intro h
    have := congrArg (fun v => v.getLsbD 0) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    cases i with
    | zero => simpa using h
    | succ i => simp

theorem P_stepBit (s : UInt32) :
    P (stepBit s) = P s * X + if s.toBitVec.getLsbD 0 then G else 0 := by
  have h := polyR_mul_X s.toBitVec
  have h2 := CharTwo.add_self_eq_zero (X ^ 32 : (ZMod 2)[X])
  unfold stepBit
  rw [P_xor, h]
  have e1 : (s >>> 1).toBitVec = s.toBitVec >>> 1 := by simp
  have e2 : (0x82F63B78 : UInt32).toBitVec = 0x82F63B78#32 := rfl
  have e3 : (0 : UInt32).toBitVec = 0#32 := rfl
  by_cases hb : s.toBitVec.getLsbD 0 = true
  · have hc : s &&& 1 = 1 := (and_one_eq_one_iff s).mpr hb
    simp only [hc, hb, ↓reduceIte, G_eq, P, e1, e2]
    linear_combination -h2
  · have hc : ¬ (s &&& 1 = 1) := fun h => hb ((and_one_eq_one_iff s).mp h)
    simp only [hc, hb, ↓reduceIte, P, e1, e3]
    simp
    exact polyR_zero

theorem π_P_stepBit (s : UInt32) : π (P (stepBit s)) = π (P s) * π X := by
  rw [P_stepBit]; split <;> simp [π_G]

/-- Zero-extension multiplies the reflected view by a power of `X`. -/
theorem polyR_setWidth {w m : Nat} (h : w ≤ m) (v : BitVec w) :
    polyR (v.setWidth m) = polyR v * X ^ (m - w) := by
  ext k
  rw [coeff_mul_X_pow', coeff_polyR, coeff_polyR, BitVec.getLsbD_setWidth]
  by_cases h1 : m - w ≤ k
  · by_cases h2 : k < m
    · have e : w - 1 - (k - (m - w)) = m - 1 - k := by omega
      have h3 : k - (m - w) < w := by omega
      have h4 : m - 1 - k < m := by omega
      simp [h1, h2, e, h3, h4]
    · have h3 : ¬ k - (m - w) < w := by omega
      simp [h1, h2, h3]
  · have : w ≤ m - 1 - k := by omega
    simp [h1, BitVec.getLsbD_of_ge _ _ this]

theorem π_P_stepByte (s : UInt32) (b : UInt8) :
    π (P (stepByte s b)) = π (P s) * π X ^ 8 + π (polyR b.toBitVec) * π X ^ 32 := by
  unfold stepByte
  simp only [π_P_stepBit, P_xor, map_add]
  have : P b.toUInt32 = polyR b.toBitVec * X ^ 24 := by
    simp [P, polyR_setWidth]
  rw [this, map_mul, map_pow]
  ring

theorem π_P_rawExtend (s : UInt32) (bs : List UInt8) :
    π (P (rawExtend s bs)) = π (P s) * π X ^ (8 * bs.length) + π (msgPoly bs) * π X ^ 32 := by
  induction bs generalizing s with
  | nil => simp [rawExtend, msgPoly]
  | cons b bs ih =>
    have : rawExtend s (b :: bs) = rawExtend (stepByte s b) bs := rfl
    rw [this, ih, π_P_stepByte]
    simp only [msgPoly, List.length_cons, map_add, map_mul, map_pow]
    ring

theorem getLsbD_bitsR (p : (ZMod 2)[X]) (i : Nat) :
    (bitsR p).getLsbD i = decide (i < 32 ∧ p.coeff (31 - i) = 1) := by
  unfold bitsR
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  by_cases hi : i < 32
  · simp [hi]
  · simp [hi]

theorem polyR_bitsR {p : (ZMod 2)[X]} (hp : p.degree < 32) : polyR (bitsR p) = p := by
  ext k
  rw [coeff_polyR, getLsbD_bitsR]
  by_cases hk : k < 32
  · have e : 31 - (32 - 1 - k) = k := by omega
    have h1 : 32 - 1 - k < 32 := by omega
    simp only [hk, h1, e, true_and, decide_eq_true_eq]
    generalize p.coeff k = c
    revert c; decide
  · have : p.coeff k = 0 :=
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast not_lt.mp hk))
    simp [hk, this]

theorem bitsR_polyR (v : BitVec 32) : bitsR (polyR v) = v :=
  polyR_injective (polyR_bitsR (degree_polyR_lt v))

/-! ### The executable reference equals the spec -/

theorem rawExtend_eq_spec (s : UInt32) (bs : List UInt8) :
    rawExtend s bs = Spec.rawExtend s bs := by
  unfold Spec.rawExtend
  rw [modByMonic_eq_of_π_eq (degree_P_lt (rawExtend s bs))]
  · rw [bitsR_polyR]
  · rw [π_P_rawExtend]; simp

theorem extend_eq_spec (c : UInt32) (bs : ByteArray) : extend c bs = Spec.extend c bs := by
  simp [extend, Spec.extend, rawExtend_eq_spec]

theorem crc32c_eq_spec (bs : ByteArray) : crc32c bs = Spec.crc32c bs :=
  extend_eq_spec 0 bs

end Crc32c
