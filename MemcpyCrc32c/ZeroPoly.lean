/-
Certified sparse multiples of the generator ("zero polynomials", after Chorba).
Candidates come from the untrusted offline search in `scripts/`; each one kept
here is proven to be a multiple of `G` by kernel evaluation of `powMod`, with
no `native_decide`.

`G` has an even number of terms, so `X + 1` divides it and every multiple has
even weight: unlike the gzip polynomial there are no 3- or 5-term multiples.
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

/-- Every multiple of `G` vanishes at 1, so it has an even number of terms. -/
theorem eval_one_G : G.eval 1 = 0 := by
  simp [G]; decide

/-- The lowest-degree 6-term multiple of `G` (search bound: degree ≤ 400). -/
theorem zero6_209 : G ∣ X ^ 209 + X ^ 144 + X ^ 54 + X ^ 39 + X ^ 14 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 209 ^^^ powMod x1 144 ^^^ powMod x1 54 ^^^ powMod x1 39 ^^^
      powMod x1 14 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 6-term multiple of `G` whose first gap exceeds two 64-bit
words (`290 - 136 = 154 ≥ 128`), so a 5-word Chorba window shifts `n1' = n2`
with zero bit operations on the leading word. -/
theorem zero6_290 : G ∣ X ^ 290 + X ^ 136 + X ^ 113 + X ^ 107 + X ^ 32 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 290 ^^^ powMod x1 136 ^^^ powMod x1 113 ^^^ powMod x1 107 ^^^
      powMod x1 32 ^^^ 0x80000000 = 0 := by decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The lowest-degree 4-term multiple of `G` (search bound: degree ≤ 6000). -/
theorem zero4_5275 : G ∣ X ^ 5275 + X ^ 4508 + X ^ 2751 + 1 := by
  apply dvd_of_π_eq_zero
  have h : powMod x1 5275 ^^^ powMod x1 4508 ^^^ powMod x1 2751 ^^^ 0x80000000 = 0 := by
    decide +kernel
  have := congrArg (fun s => π (P s)) h
  simpa only [P_xor, map_add, ← π_X_pow, P_one, P_zero, map_one, map_zero, map_pow] using this

/-- The core Chorba lemma: adding any multiple of a zero polynomial to the
message leaves the remainder unchanged. -/
theorem modByMonic_add_zeroPoly_mul {Z : (ZMod 2)[X]} (hZ : G ∣ Z) (M c : (ZMod 2)[X]) (k : Nat) :
    (M + Z * X ^ k * c) %ₘ G = M %ₘ G := by
  apply modByMonic_eq_of_π_eq
  · have := degree_modByMonic_lt M G_monic; rwa [G_degree] at this
  · obtain ⟨q, rfl⟩ := hZ
    simp [π_modByMonic, π_G]

end Crc32c
