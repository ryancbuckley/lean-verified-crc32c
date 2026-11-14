/-
The Castagnoli generator and the quotient map used for every "equal modulo G"
argument in the project. The GF(2) polynomial views of bit-vectors (`ofBits`,
`polyR`, `polyN`) live in the `lean-simd-models` package and are re-exported
here unchanged (move approved 2026-11-14).
-/
import SimdModels.Poly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod

namespace Crc32c
open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

export SimdModels (ofBits coeff_ofBits degree_ofBits_lt polyR polyN coeff_polyR degree_polyR_lt polyR_xor polyR_zero polyR_mul_X polyR_injective)

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
