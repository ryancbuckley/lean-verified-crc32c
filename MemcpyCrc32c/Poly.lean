/-
GF(2) polynomial views of bit-vectors, the Castagnoli generator, and the
quotient map used for every "equal modulo G" argument in the project.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod

namespace Crc32c
open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The polynomial over GF(2) whose `X^k` coefficient is `f k`, for `k < n`. -/
def ofBits (n : Nat) (f : Nat → Bool) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if f i then X ^ i else 0

theorem coeff_ofBits (n : Nat) (f : Nat → Bool) (k : Nat) :
    (ofBits n f).coeff k = if k < n ∧ f k then 1 else 0 := by
  simp only [ofBits, finsetSum_coeff, apply_ite (fun p : (ZMod 2)[X] => p.coeff k),
    coeff_X_pow, coeff_zero]
  by_cases hk : k < n
  · rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; simp [hk] at h
  · rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro i hi
      have : k ≠ i := by have := Finset.mem_range.mp hi; omega
      simp [this]

theorem degree_ofBits_lt (n : Nat) (f : Nat → Bool) : (ofBits n f).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_ofBits]
  simp; omega

/-- Reflected view: bit `w-1` is the constant term, bit `0` is `X^(w-1)`.
This is the CRC32C convention for both the 32-bit state and message bytes. -/
def polyR {w : Nat} (v : BitVec w) : (ZMod 2)[X] :=
  ofBits w (fun k => v.getLsbD (w - 1 - k))

/-- Natural view: bit `k` is the coefficient of `X^k`. -/
def polyN {w : Nat} (v : BitVec w) : (ZMod 2)[X] :=
  ofBits w v.getLsbD

theorem coeff_polyR {w : Nat} (v : BitVec w) (k : Nat) :
    (polyR v).coeff k = if k < w ∧ v.getLsbD (w - 1 - k) then 1 else 0 :=
  coeff_ofBits ..

theorem degree_polyR_lt {w : Nat} (v : BitVec w) : (polyR v).degree < w :=
  degree_ofBits_lt ..

theorem polyR_xor {w : Nat} (a b : BitVec w) : polyR (a ^^^ b) = polyR a + polyR b := by
  ext k
  simp only [coeff_add, coeff_polyR, BitVec.getLsbD_xor]
  by_cases hk : k < w <;> cases a.getLsbD (w - 1 - k) <;> cases b.getLsbD (w - 1 - k) <;>
    simp [hk]
  all_goals decide

theorem polyR_zero {w : Nat} : polyR (0 : BitVec w) = 0 := by
  ext k; simp [coeff_polyR]

/-- Shifting right by one multiplies by `X`, dropping the `X^w` overflow. -/
theorem polyR_mul_X {w : Nat} (v : BitVec w) :
    polyR v * X = polyR (v >>> 1) + if v.getLsbD 0 then X ^ w else 0 := by
  ext k
  rw [coeff_add, apply_ite (fun p : (ZMod 2)[X] => p.coeff k), coeff_X_pow, coeff_zero]
  cases k with
  | zero =>
    simp only [coeff_mul_X_zero, coeff_polyR, BitVec.getLsbD_ushiftRight]
    by_cases hw : w = 0
    · subst hw; simp
    · simp [Ne.symm hw]
      intro _; apply BitVec.getLsbD_of_ge; omega
  | succ k =>
    simp only [coeff_mul_X, coeff_polyR, BitVec.getLsbD_ushiftRight]
    by_cases hk : k + 1 < w
    · have h1 : 1 + (w - 1 - (k + 1)) = w - 1 - k := by omega
      have h2 : k + 1 ≠ w := by omega
      have h3 : k < w := by omega
      simp [hk, h1, h2, h3]
    · by_cases hk' : k + 1 = w
      · subst hk'; simp
      · have h3 : ¬ k < w := by omega
        simp [hk, hk', h3]

theorem polyR_injective {w : Nat} : Function.Injective (polyR (w := w)) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun p => p.coeff (w - 1 - i)) h
  simp only [coeff_polyR] at this
  have h1 : w - 1 - i < w := by omega
  have h2 : w - 1 - (w - 1 - i) = i := by omega
  simp only [h1, h2, true_and] at this
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp [ha, hb] at this <;> rfl

/-! ### The Castagnoli generator -/

/-- The CRC32C (Castagnoli) generator polynomial, `0x1EDC6F41` plus the leading `X^32`. -/
def G : (ZMod 2)[X] :=
  X^32 + X^28 + X^27 + X^26 + X^25 + X^23 + X^22 + X^20 + X^19 + X^18 + X^14 + X^13 +
    X^11 + X^10 + X^9 + X^8 + X^6 + 1

set_option maxRecDepth 100000 in
/-- `G` minus its leading term is the reflected constant `0x82F63B78`. -/
theorem G_eq : G = X^32 + polyR (0x82F63B78#32) := by
  simp +decide [G, polyR, ofBits, Finset.sum_range_succ, BitVec.getLsbD]
  ring

theorem G_monic : G.Monic := by
  rw [G_eq]; exact monic_X_pow_add (degree_polyR_lt _)

theorem G_degree : G.degree = 32 := by
  rw [G_eq, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_polyR_lt _),
    degree_X_pow]; rfl

/-- Residues modulo `G`. All congruence reasoning happens in this ring. -/
abbrev Q := AdjoinRoot G

/-- The quotient map `GF(2)[X] → GF(2)[X]/(G)`. -/
def π : (ZMod 2)[X] →+* Q := AdjoinRoot.mk G

theorem π_modByMonic (p : (ZMod 2)[X]) : π (p %ₘ G) = π p := by
  conv_rhs => rw [← modByMonic_add_div p G]
  simp [π]

theorem π_G : π G = 0 := by simp [π]

/-- Two polynomials of degree `< 32` that agree modulo `G` are equal. -/
theorem eq_of_π_eq {p q : (ZMod 2)[X]} (hp : p.degree < 32) (hq : q.degree < 32)
    (h : π p = π q) : p = q := by
  rw [π, AdjoinRoot.mk_eq_mk] at h
  have hd : (p - q).degree < G.degree := by
    rw [G_degree]; exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hp hq)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt h hd)

theorem modByMonic_eq_of_π_eq {p r : (ZMod 2)[X]} (hr : r.degree < 32)
    (h : π r = π p) : p %ₘ G = r := by
  refine eq_of_π_eq ?_ hr ?_
  · have := degree_modByMonic_lt p G_monic; rwa [G_degree] at this
  · rw [π_modByMonic, h]

theorem Q_add_self (a : Q) : a + a = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [← map_add, CharTwo.add_self_eq_zero, map_zero]

end

end Crc32c
