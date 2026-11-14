/-
How word shifts act on the reflected polynomial view. Kernel-only proofs.
-/
import SimdModels.Poly

namespace SimdModels
open Polynomial

/-- Moving a word `r` bits later in the stream, seen in a two-word window:
`v <<< r` stays in the first word and `v >>> (w - r)` spills into the second. -/
theorem polyR_shiftLeft_add_shiftRight {w : Nat} (v : BitVec w) (r : Nat) (hr : r ≤ w) :
    polyR (v <<< r) * X ^ w + polyR (v >>> (w - r)) = polyR v * X ^ (w - r) := by
  ext k
  rw [coeff_add, coeff_mul_X_pow', coeff_mul_X_pow', coeff_polyR, coeff_polyR, coeff_polyR,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases hk : w ≤ k
  · have h0 : ¬ k < w := by omega
    have h1 : w - r ≤ k := by omega
    by_cases hk2 : k - w < w
    · by_cases hj : w - 1 - (k - w) < r
      · have h2 : ¬ k - (w - r) < w := by omega
        simp [hk, h0, h1, hk2, hj, h2]
      · have h2 : k - (w - r) < w := by omega
        have h3 : w - 1 - (k - w) < w := by omega
        have h4 : w - 1 - (k - w) - r = w - 1 - (k - (w - r)) := by omega
        simp [hk, h0, h1, hk2, hj, h2, h3, h4]
    · have h2 : ¬ k - (w - r) < w := by omega
      simp [hk, h0, h1, hk2, h2]
  · have h0 : k < w := by omega
    by_cases h1 : w - r ≤ k
    · have h2 : k - (w - r) < w := by omega
      have h4 : w - r + (w - 1 - k) = w - 1 - (k - (w - r)) := by omega
      simp [hk, h0, h1, h2, h4]
    · have h5 : w ≤ w - r + (w - 1 - k) := by omega
      simp [hk, h0, h1, BitVec.getLsbD_of_ge _ _ h5]

/-- A zero-extended value shifted left stays a single shifted copy. -/
theorem polyR_setWidth_shiftLeft {w m s : Nat} (h : w + s ≤ m) (v : BitVec w) :
    polyR (v.setWidth m <<< s) = polyR v * X ^ (m - w - s) := by
  ext k
  rw [coeff_mul_X_pow', coeff_polyR, coeff_polyR, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  by_cases hk : k < m
  · have h3 : m - 1 - k < m := by omega
    by_cases h4 : m - 1 - k < s
    · by_cases h1 : m - w - s ≤ k
      · have h2 : ¬ k - (m - w - s) < w := by omega
        simp [hk, h1, h2, h3, h4]
      · simp [hk, h1, h3, h4]
    · by_cases h1 : m - w - s ≤ k
      · have h2 : k - (m - w - s) < w := by omega
        have h6 : m - 1 - k - s = w - 1 - (k - (m - w - s)) := by omega
        have h8 : w - 1 - (k - (m - w - s)) < m := by omega
        simp [hk, h1, h2, h3, h4, h6, h8]
      · have h7 : w ≤ m - 1 - k - s := by omega
        simp [hk, h1, h3, h4, BitVec.getLsbD_of_ge _ _ h7]
  · by_cases h1 : m - w - s ≤ k
    · have h2 : ¬ k - (m - w - s) < w := by omega
      simp [hk, h1, h2]
    · simp [hk, h1]

end SimdModels
