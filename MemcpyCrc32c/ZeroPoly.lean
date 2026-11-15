/-
Certified sparse multiples of the generator ("zero polynomials", after Chorba).
Candidates come from the untrusted offline search in `scripts/`; each one kept
here is proven to be a multiple of `G` by kernel evaluation of `powMod`, with
no `native_decide`. Minimality and uniqueness at each weight are proven in
`MemcpyCrc32c.PolyAlgebra` (weight 2) and `MemcpyCrc32c.ZeroPolyMinimal`
(weights 4, 6, and 8).

`G` has an even number of terms, so `X + 1` divides it and every multiple has
even weight (`even_card_support_of_dvd_G`): unlike the gzip polynomial there
are no odd-weight multiples at any degree.
-/
import MemcpyCrc32c.Arith

namespace Crc32c
open Polynomial

/-- `X`, reflected. -/
def x1 : UInt32 := 0x40000000

theorem P_x1 : P x1 = X := by
  change polyR (BitVec.twoPow 32 30) = X
  simp [polyR_twoPow]

theorem π_X_pow (n : Nat) : π X ^ n = π (P (powMod x1 n)) := by
  rw [π_P_powMod, P_x1]

theorem dvd_of_π_eq_zero {p : (ZMod 2)[X]} (h : π p = 0) : G ∣ p :=
  AdjoinRoot.mk_eq_zero.mp h

/-- Every multiple of `G` vanishes at 1. -/
theorem eval_one_G : G.eval 1 = 0 := by
  simp [G]; decide

/-- Over `ZMod 2`, every polynomial is the sum of the monomials in its support. -/
theorem as_sum_support_X_pow (p : (ZMod 2)[X]) :
    p = ∑ s ∈ p.support, (X : (ZMod 2)[X]) ^ s := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hc : p.coeff s = 1 := by
    have hne := mem_support_iff.mp hs
    generalize p.coeff s = c at hne
    revert c; decide
  rw [hc]; simp

/-- Over `ZMod 2`, evaluating at `1` computes the parity of the number of terms. -/
theorem eval_one_eq_card_support (p : (ZMod 2)[X]) :
    p.eval 1 = (p.support.card : ZMod 2) := by
  conv_lhs => rw [as_sum_support_X_pow p]
  simp [eval_finsetSum]

/-- Every multiple of `G` has an even number of nonzero terms. -/
theorem even_card_support_of_dvd_G {p : (ZMod 2)[X]} (hG : G ∣ p) :
    Even p.support.card := by
  obtain ⟨q, rfl⟩ := hG
  have h0 : (G * q).eval 1 = 0 := by simp [eval_one_G]
  rw [eval_one_eq_card_support, ZMod.natCast_eq_zero_iff] at h0
  exact even_iff_two_dvd.mpr h0

/-- No multiple of `G` has an odd number of terms (1, 3, 5, 7, …). -/
theorem not_odd_card_support_of_dvd_G {p : (ZMod 2)[X]} (hG : G ∣ p) :
    ¬ Odd p.support.card :=
  Nat.not_odd_iff_even.mpr (even_card_support_of_dvd_G hG)

/-- The lowest-degree 2-term multiple of `G` (`2^31 - 1 = 2147483647`).
Minimality and uniqueness are proven in `MemcpyCrc32c.PolyAlgebra`
(`zero2_minimal`, `zero2_unique`). -/
theorem zero2_mersenne : G ∣ X ^ 2147483647 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 2147483647 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 4-term multiple of `G`. Minimality and uniqueness are
proven in `MemcpyCrc32c.ZeroPolyMinimal` (`zero4_5275_minimal`,
`zero4_5275_unique`). -/
theorem zero4_5275 : G ∣ X ^ 5275 + X ^ 4508 + X ^ 2751 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 5275 ^^^ powMod x1 4508 ^^^ powMod x1 2751 ^^^ 0x80000000 = 0 := by
    decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 6-term multiple of `G`. Minimality and uniqueness are
proven in `MemcpyCrc32c.ZeroPolyMinimal` (`zero6_209_minimal`,
`zero6_209_unique`). -/
theorem zero6_209 : G ∣ X ^ 209 + X ^ 144 + X ^ 54 + X ^ 39 + X ^ 14 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 209 ^^^ powMod x1 144 ^^^ powMod x1 54 ^^^ powMod x1 39 ^^^
      powMod x1 14 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 6-term multiple of `G` whose first gap exceeds two 64-bit
words (`290 - 136 = 154 ≥ 128`), so a 5-word Chorba window shifts `n1' = n2`
with zero bit operations on the leading word. Minimality and uniqueness are
proven in `MemcpyCrc32c.ZeroPolyMinimal` (`zero6_290_minimal`,
`zero6_290_unique`). -/
theorem zero6_290 : G ∣ X ^ 290 + X ^ 136 + X ^ 113 + X ^ 107 + X ^ 32 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 290 ^^^ powMod x1 136 ^^^ powMod x1 113 ^^^ powMod x1 107 ^^^
      powMod x1 32 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 8-term multiple of `G`. Minimality and uniqueness are
proven in `MemcpyCrc32c.ZeroPolyMinimal` (`zero8_79_minimal`,
`zero8_79_unique`). -/
theorem zero8_79 : G ∣ X ^ 79 + X ^ 75 + X ^ 71 + X ^ 58 + X ^ 18 + X ^ 12 + X + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 79 ^^^ powMod x1 75 ^^^ powMod x1 71 ^^^ powMod x1 58 ^^^
      powMod x1 18 ^^^ powMod x1 12 ^^^ x1 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_x1, P_one, P_zero, map_one, map_zero, map_pow]
    using this

/-- The core Chorba lemma: adding any multiple of a zero polynomial to the
message leaves the remainder unchanged. -/
theorem modByMonic_add_zeroPoly_mul {Z : (ZMod 2)[X]} (hZ : G ∣ Z) (M c : (ZMod 2)[X]) (k : Nat) :
    (M + Z * X ^ k * c) %ₘ G = M %ₘ G := by
  apply modByMonic_eq_of_π_eq
  · have := degree_modByMonic_lt M G_monic; rwa [G_degree] at this
  · obtain ⟨q, rfl⟩ := hZ
    simp [π_modByMonic, π_G]

end Crc32c
