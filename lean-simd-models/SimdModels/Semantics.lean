/-
Semantic lemmas: what each instruction model computes, as GF(2) polynomial
arithmetic. Proof module (Mathlib). Kernel-only proofs.
-/
import SimdModels.Poly
import SimdModels.PolyShift
import SimdModels.Models
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Reverse

namespace SimdModels
open Polynomial

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ### The natural view -/

theorem coeff_polyN {w : Nat} (v : BitVec w) (k : Nat) :
    (polyN v).coeff k = if k < w ∧ v.getLsbD k then 1 else 0 :=
  coeff_ofBits ..

theorem degree_polyN_lt {w : Nat} (v : BitVec w) : (polyN v).degree < w :=
  degree_ofBits_lt ..

theorem coeff_polyN' {w : Nat} (v : BitVec w) (k : Nat) :
    (polyN v).coeff k = if v.getLsbD k then 1 else 0 := by
  rw [coeff_polyN]
  by_cases hk : k < w
  · simp [hk]
  · simp [hk, BitVec.getLsbD_of_ge v k (by omega)]

theorem polyN_xor {w : Nat} (a b : BitVec w) : polyN (a ^^^ b) = polyN a + polyN b := by
  ext k
  simp only [coeff_add, coeff_polyN', BitVec.getLsbD_xor]
  cases a.getLsbD k <;> cases b.getLsbD k <;> simp
  decide

theorem polyN_zero {w : Nat} : polyN (0 : BitVec w) = 0 := by
  ext k; simp [coeff_polyN']

theorem polyN_cast {w v : Nat} (h : w = v) (x : BitVec w) : polyN (x.cast h) = polyN x := by
  subst h; rfl

/-- Bit reversal swaps the two views. -/
theorem polyN_reverse {w : Nat} (v : BitVec w) : polyN v.reverse = polyR v := by
  ext k
  rw [coeff_polyN, coeff_polyR, BitVec.getLsbD_reverse, BitVec.getMsbD]
  by_cases hk : k < w <;> simp [hk]

theorem polyR_reverse {w : Nat} (v : BitVec w) : polyR v.reverse = polyN v := by
  ext k
  rw [coeff_polyN, coeff_polyR, BitVec.getLsbD_reverse, BitVec.getMsbD]
  by_cases hk : k < w
  · have h1 : w - 1 - k < w := by omega
    have h2 : w - 1 - (w - 1 - k) = k := by omega
    simp [hk, h1, h2]
  · simp [hk]

/-- `a : b` in ASL: `a` is the high part. -/
theorem polyN_append {n m : Nat} (a : BitVec n) (b : BitVec m) :
    polyN (a ++ b) = polyN a * X ^ m + polyN b := by
  ext k
  rw [coeff_add, coeff_mul_X_pow', coeff_polyN', coeff_polyN', coeff_polyN', BitVec.getLsbD_append]
  by_cases hk : k < m
  · have : ¬ m ≤ k := by omega
    simp [hk, this]
  · have h1 : m ≤ k := by omega
    simp [hk, h1]

/-- Truncating to `j + 1` bits adds bit `j`. -/
theorem polyN_setWidth_succ {w : Nat} (x : BitVec w) (j : Nat) :
    polyN (x.setWidth (j + 1)) = polyN (x.setWidth j) + if x.getLsbD j then X ^ j else 0 := by
  ext k
  rw [coeff_add, apply_ite (fun p : (ZMod 2)[X] => p.coeff k), coeff_X_pow, coeff_zero,
    coeff_polyN', coeff_polyN', BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
  by_cases h1 : k < j
  · have h2 : k < j + 1 := by omega
    have h3 : k ≠ j := by omega
    simp [h1, h2, h3]
  · by_cases h3 : k = j
    · subst h3; cases x.getLsbD k <;> simp
    · have h2 : ¬ k < j + 1 := by omega
      simp [h1, h2, h3]

theorem polyN_setWidth_zero {w : Nat} (x : BitVec w) : polyN (x.setWidth 0) = 0 := by
  ext k; simp [coeff_polyN]

theorem polyN_setWidth_self {w : Nat} (x : BitVec w) : polyN (x.setWidth w) = polyN x := by
  simp

theorem polyN_setWidth_xor {w : Nat} (x y : BitVec w) (j : Nat) :
    polyN ((x ^^^ y).setWidth j) = polyN (x.setWidth j) + polyN (y.setWidth j) := by
  rw [BitVec.setWidth_xor, polyN_xor]

/-- A zero-extended value shifted left, seen through a window wide enough to hold it. -/
theorem polyN_setWidth_shiftLeft {w n : Nat} (p : BitVec w) (k j : Nat) (hj : w + k ≤ j)
    (hn : j ≤ n) : polyN ((p.setWidth n <<< k).setWidth j) = polyN p * X ^ k := by
  ext i
  rw [coeff_mul_X_pow', coeff_polyN', coeff_polyN', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : k ≤ i
  · by_cases h2 : i - k < w
    · have h3 : i < j := by omega
      have h4 : i < n := by omega
      have h5 : ¬ i < k := by omega
      have h6 : i - k < n := by omega
      simp [h1, h3, h4, h5, h6]
    · simp [h1, BitVec.getLsbD_of_ge p (i - k) (by omega)]
  · have h5 : i < k := by omega
    simp [h1, h5]

/-! ### CRC32C -/

/-- The CRC32C generator as the manuals give it: `X^32` plus the constant `0x1EDC6F41`. -/
noncomputable def castagnoli : (ZMod 2)[X] := X ^ 32 + polyN Model.crc32cPoly

theorem castagnoli_monic : castagnoli.Monic :=
  monic_X_pow_add (degree_polyN_lt _)

theorem castagnoli_degree : castagnoli.degree = 32 := by
  rw [castagnoli, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_polyN_lt _),
    degree_X_pow]; rfl

/-- Loop invariant of `Poly32Mod2`: the low `32 + k` bits keep their residue. -/
theorem poly32Mod2Loop_spec {n : Nat} (k : Nat) (hk : 32 + k ≤ n) (data : BitVec n) :
    polyN ((Model.poly32Mod2Loop Model.crc32cPoly k data).setWidth 32) %ₘ castagnoli =
      polyN (data.setWidth (32 + k)) %ₘ castagnoli := by
  induction k generalizing data with
  | zero => rfl
  | succ k ih =>
    rw [Model.poly32Mod2Loop, ih (by omega)]
    apply modByMonic_eq_of_dvd_sub castagnoli_monic
    rw [show 32 + (k + 1) = (32 + k) + 1 by omega, polyN_setWidth_succ]
    by_cases hb : data.getLsbD (32 + k) = true
    · simp only [hb, ↓reduceIte]
      rw [polyN_setWidth_xor, polyN_setWidth_shiftLeft _ _ _ (by omega) (by omega)]
      refine ⟨X ^ k, ?_⟩
      have h3 := CharTwo.add_self_eq_zero (X ^ (32 + k) : (ZMod 2)[X])
      rw [castagnoli]
      linear_combination -h3
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, add_zero, sub_self, dvd_zero]

theorem poly32Mod2_spec {n : Nat} (hn : 32 ≤ n) (data : BitVec n) :
    polyN (Model.poly32Mod2 data Model.crc32cPoly) = polyN data %ₘ castagnoli := by
  have h := poly32Mod2Loop_spec (n - 32) (by omega) data
  rw [show 32 + (n - 32) = n by omega, polyN_setWidth_self] at h
  rw [← h, Model.poly32Mod2]
  symm
  rw [modByMonic_eq_self_iff castagnoli_monic, castagnoli_degree]
  exact degree_polyN_lt _

/-- What the CRC32C instruction computes: absorb `size` message bits into the
reflected state, modulo the Castagnoli generator. -/
theorem crc32c_spec (size : Nat) (acc : BitVec 32) (val : BitVec size) :
    polyR (Model.crc32c size acc val) =
      (polyR acc * X ^ size + polyR val * X ^ 32) %ₘ castagnoli := by
  rw [Model.crc32c, polyR_reverse, poly32Mod2_spec (by omega), polyN_xor, polyN_append,
    polyN_cast, polyN_append, polyN_zero, polyN_zero, polyN_reverse, polyN_reverse]
  simp

/-! ### Carry-less multiply -/

theorem polynomialMultLoop_spec (a : BitVec 64) (b : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    polyN (Model.polynomialMultLoop a (b.setWidth 128) k) = polyN (a.setWidth k) * polyN b := by
  induction k with
  | zero =>
    simp [Model.polynomialMultLoop, polyN_setWidth_zero]
    exact polyN_zero
  | succ k ih =>
    rw [Model.polynomialMultLoop, polyN_setWidth_succ]
    have hs : polyN (b.setWidth 128 <<< k) = polyN b * X ^ k := by
      have := polyN_setWidth_shiftLeft (n := 128) b k 128 (by omega) (by omega)
      rwa [BitVec.setWidth_eq] at this
    by_cases hb : a.getLsbD k = true
    · simp only [hb, ↓reduceIte, polyN_xor, hs, ih (by omega)]
      ring
    · simp [hb, ih (by omega)]

/-- `PMULL` / `PCLMULQDQ` multiply the natural polynomial views. -/
theorem polynomialMult_spec (a b : BitVec 64) :
    polyN (Model.polynomialMult a b) = polyN a * polyN b := by
  rw [Model.polynomialMult, polynomialMultLoop_spec a b 64 (by omega), polyN_setWidth_self]

/-- A 128-bit value is its low half plus `X^64` times its high half. -/
theorem polyN_halves (x : BitVec 128) :
    polyN x = polyN (x.setWidth 64) + polyN ((x >>> 64).setWidth 64) * X ^ 64 := by
  ext k
  rw [coeff_add, coeff_mul_X_pow', coeff_polyN', coeff_polyN', coeff_polyN',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases hk : k < 64
  · have : ¬ 64 ≤ k := by omega
    simp [hk, this]
  · have h1 : 64 ≤ k := by omega
    by_cases h2 : k - 64 < 64
    · have h3 : 64 + (k - 64) = k := by omega
      simp [hk, h1, h2, h3]
    · simp [hk, h1, h2, BitVec.getLsbD_of_ge x k (by omega)]

/-- The two halves of the carry-less product, natural view. -/
theorem clmul_spec (a b : UInt64) :
    polyN (Model.clmulLo a b).toBitVec + polyN (Model.clmulHi a b).toBitVec * X ^ 64 =
      polyN a.toBitVec * polyN b.toBitVec := by
  simp only [Model.clmulLo, Model.clmulHi]
  rw [← polynomialMult_spec, polyN_halves (Model.polynomialMult a.toBitVec b.toBitVec)]

/-! ### Carry-less multiply on bit-reflected data

CRC kernels hold data bit-reflected. Multiplying two reflected 64-bit values
gives the reflected product shifted by one: the extra factor `X`. -/

theorem natDegree_polyN_le {w : Nat} (v : BitVec w) : (polyN v).natDegree ≤ w - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_polyN]
  have : ¬ N < w := by omega
  simp [this]

/-- The reflected view is the polynomial reversal of the natural view. -/
theorem polyR_eq_reflect {w : Nat} (v : BitVec w) : polyR v = reflect (w - 1) (polyN v) := by
  ext k
  rw [coeff_reflect, coeff_polyR, coeff_polyN]
  by_cases hk : k ≤ w - 1
  · rw [revAt_le hk]
    by_cases hw : w = 0
    · subst hw; simp
    · have h1 : k < w := by omega
      have h2 : w - 1 - k < w := by omega
      simp [h1, h2]
  · have h1 : ¬ k < w := by omega
    have h2 : revAt (w - 1) k = k := revAt_eq_self_of_lt (by omega)
    simp [h1, h2]

theorem reflect_succ_of_natDegree_le (N : Nat) (p : (ZMod 2)[X]) (hp : p.natDegree ≤ N) :
    reflect (N + 1) p = X * reflect N p := by
  ext k
  rw [coeff_reflect]
  cases k with
  | zero =>
    rw [coeff_X_mul_zero, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  | succ j =>
    rw [coeff_X_mul, coeff_reflect]
    by_cases hj : j ≤ N
    · rw [revAt_le (by omega), revAt_le hj]
      congr 1
      omega
    · have e1 : revAt (N + 1) (j + 1) = j + 1 := revAt_eq_self_of_lt (by omega)
      have e2 : revAt N j = j := revAt_eq_self_of_lt (by omega)
      rw [e1, e2, coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_eq_zero_of_natDegree_lt (by omega)]

/-- A 128-bit value in the reflected view: the low half is the high-degree part. -/
theorem polyR_halves (x : BitVec 128) :
    polyR x = polyR (x.setWidth 64) * X ^ 64 + polyR ((x >>> 64).setWidth 64) := by
  ext k
  rw [coeff_add, coeff_mul_X_pow', coeff_polyR, coeff_polyR, coeff_polyR,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases hk : k < 64
  · have h1 : ¬ 64 ≤ k := by omega
    have h2 : k < 128 := by omega
    have h3 : 64 - 1 - k < 64 := by omega
    have h4 : 64 + (64 - 1 - k) = 128 - 1 - k := by omega
    simp [hk, h1, h2, h3, h4]
  · have h1 : 64 ≤ k := by omega
    by_cases h2 : k < 128
    · have h3 : k - 64 < 64 := by omega
      have h4 : 64 - 1 - (k - 64) < 64 := by omega
      have h5 : 64 - 1 - (k - 64) = 128 - 1 - k := by omega
      have h6 : 127 - k < 64 := by omega
      simp [hk, h1, h2, h3, h5, h6]
    · have h3 : ¬ k - 64 < 64 := by omega
      simp [hk, h1, h2, h3]

/-- The two halves of the carry-less product, reflected view. -/
theorem clmul_spec_reflected (a b : UInt64) :
    polyR (Model.clmulLo a b).toBitVec * X ^ 64 + polyR (Model.clmulHi a b).toBitVec =
      X * (polyR a.toBitVec * polyR b.toBitVec) := by
  simp only [Model.clmulLo, Model.clmulHi]
  rw [← polyR_halves, polyR_eq_reflect, polynomialMult_spec, polyR_eq_reflect a.toBitVec,
    polyR_eq_reflect b.toBitVec]
  have ha := natDegree_polyN_le a.toBitVec
  have hb := natDegree_polyN_le b.toBitVec
  rw [← reflect_mul _ _ ha hb]
  exact reflect_succ_of_natDegree_le 126 _ (le_trans natDegree_mul_le (by omega))

end SimdModels
