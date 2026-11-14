/-
Fixed-width byte and word identities for `MemcpyCrc32c.Impl.Portable`, proven
directly in the Lean kernel via `BitVec.eq_of_getLsbD_eq` with no `bv_decide`
or extra axioms.
-/
import MemcpyCrc32c.Impl.Portable

namespace Crc32c

private theorem support_toUInt64 (b : UInt8) :
    ∀ i, 8 ≤ i → b.toUInt64.toBitVec.getLsbD i = false := by
  intro i hi
  have hb : b.toUInt64.toBitVec = b.toBitVec.setWidth 64 := by simp
  rw [hb, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge _ _ hi, Bool.and_false]

private theorem support_shiftLeft {b : UInt8} {s : UInt64} {k : Nat}
    (hs : (b.toUInt64 <<< s).toBitVec = b.toBitVec.setWidth 64 <<< k) :
    (∀ i, i < k → (b.toUInt64 <<< s).toBitVec.getLsbD i = false) ∧
    (∀ i, k + 8 ≤ i → (b.toUInt64 <<< s).toBitVec.getLsbD i = false) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hs, BitVec.getLsbD_shiftLeft]; simp [hi]
  · rw [hs, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have hge : 8 ≤ i - k := by omega
    rw [BitVec.getLsbD_of_ge _ _ hge]; simp

private theorem or_eq_xor_step {a : UInt64} {b : UInt8} {s : UInt64} {k : Nat}
    (ha : ∀ i, k ≤ i → a.toBitVec.getLsbD i = false)
    (hs : (b.toUInt64 <<< s).toBitVec = b.toBitVec.setWidth 64 <<< k) :
    a ||| (b.toUInt64 <<< s) = a ^^^ (b.toUInt64 <<< s) ∧
      ∀ i, k + 8 ≤ i → (a ||| (b.toUInt64 <<< s)).toBitVec.getLsbD i = false := by
  obtain ⟨hlo, hhi⟩ := support_shiftLeft hs
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← UInt64.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_xor, BitVec.getLsbD_or, BitVec.getLsbD_xor]
    by_cases hik : i < k
    · rw [hlo i hik]; simp
    · rw [ha i (by omega)]; simp
  · simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, ha i (by omega), hhi i hi, Bool.or_self]

/-- The byte fields of a little-endian word do not overlap, so OR is XOR. -/
theorem word64_eq_xor (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    word64 b0 b1 b2 b3 b4 b5 b6 b7 =
      b0.toUInt64 ^^^ (b1.toUInt64 <<< 8) ^^^ (b2.toUInt64 <<< 16) ^^^ (b3.toUInt64 <<< 24) ^^^
        (b4.toUInt64 <<< 32) ^^^ (b5.toUInt64 <<< 40) ^^^ (b6.toUInt64 <<< 48) ^^^
        (b7.toUInt64 <<< 56) := by
  unfold word64
  obtain ⟨e1, s1⟩ := or_eq_xor_step (a := b0.toUInt64) (support_toUInt64 b0)
    (s := 8) (k := 8) (b := b1) (by simp)
  obtain ⟨e2, s2⟩ := or_eq_xor_step s1 (s := 16) (k := 16) (b := b2) (by simp)
  obtain ⟨e3, s3⟩ := or_eq_xor_step s2 (s := 24) (k := 24) (b := b3) (by simp)
  obtain ⟨e4, s4⟩ := or_eq_xor_step s3 (s := 32) (k := 32) (b := b4) (by simp)
  obtain ⟨e5, s5⟩ := or_eq_xor_step s4 (s := 40) (k := 40) (b := b5) (by simp)
  obtain ⟨e6, s6⟩ := or_eq_xor_step s5 (s := 48) (k := 48) (b := b6) (by simp)
  obtain ⟨e7, _⟩ := or_eq_xor_step s6 (s := 56) (k := 56) (b := b7) (by simp)
  rw [e7, e6, e5, e4, e3, e2, e1]

private theorem toUInt8_toUInt64_toBitVec (v : UInt64) :
    v.toUInt8.toUInt64.toBitVec = (v.toBitVec.setWidth 8).setWidth 64 := by
  have hc : ∀ c : UInt8, c.toUInt64.toBitVec = c.toBitVec.setWidth 64 := fun _ => by simp
  have hv : v.toUInt8.toBitVec = v.toBitVec.setWidth 8 := by simp
  rw [hc, hv]

/-- A word is the little-endian combination of its own bytes. -/
theorem word64_bytes (w : UInt64) :
    word64 w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8
      (w >>> 32).toUInt8 (w >>> 40).toUInt8 (w >>> 48).toUInt8 (w >>> 56).toUInt8 = w := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have b0 : w.toUInt8.toUInt64.toBitVec = (w.toBitVec.setWidth 8).setWidth 64 :=
    toUInt8_toUInt64_toBitVec w
  have b1 : ((w >>> 8).toUInt8.toUInt64 <<< 8).toBitVec =
      ((w.toBitVec >>> 8).setWidth 8).setWidth 64 <<< 8 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b2 : ((w >>> 16).toUInt8.toUInt64 <<< 16).toBitVec =
      ((w.toBitVec >>> 16).setWidth 8).setWidth 64 <<< 16 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b3 : ((w >>> 24).toUInt8.toUInt64 <<< 24).toBitVec =
      ((w.toBitVec >>> 24).setWidth 8).setWidth 64 <<< 24 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b4 : ((w >>> 32).toUInt8.toUInt64 <<< 32).toBitVec =
      ((w.toBitVec >>> 32).setWidth 8).setWidth 64 <<< 32 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b5 : ((w >>> 40).toUInt8.toUInt64 <<< 40).toBitVec =
      ((w.toBitVec >>> 40).setWidth 8).setWidth 64 <<< 40 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b6 : ((w >>> 48).toUInt8.toUInt64 <<< 48).toBitVec =
      ((w.toBitVec >>> 48).setWidth 8).setWidth 64 <<< 48 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  have b7 : ((w >>> 56).toUInt8.toUInt64 <<< 56).toBitVec =
      ((w.toBitVec >>> 56).setWidth 8).setWidth 64 <<< 56 := by
    rw [UInt64.toBitVec_shiftLeft, toUInt8_toUInt64_toBitVec]; simp
  simp only [word64, UInt64.toBitVec_or, BitVec.getLsbD_or, b0, b1, b2, b3, b4, b5, b6, b7,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and]
  by_cases h1 : i < 8
  · simp [h1, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h2 : i < 16
  · simp [h1, h2, show i - 8 < 8 by omega, show i - 8 < 64 by omega, show 8 + (i - 8) = i by omega,
      show i < 24 by omega, show i < 32 by omega, show i < 40 by omega, show i < 48 by omega,
      show i < 56 by omega]
  by_cases h3 : i < 24
  · simp [h1, h2, h3, show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega,
      show i - 16 < 64 by omega, show 16 + (i - 16) = i by omega, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h4 : i < 32
  · simp [h1, h2, h3, h4, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show i - 24 < 8 by omega, show i - 24 < 64 by omega, show 24 + (i - 24) = i by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h5 : i < 40
  · simp [h1, h2, h3, h4, h5, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show ¬ i - 24 < 8 by omega, show i - 32 < 8 by omega, show i - 32 < 64 by omega,
      show 32 + (i - 32) = i by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h6 : i < 48
  · simp [h1, h2, h3, h4, h5, h6, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega, show i - 40 < 8 by omega,
      show i - 40 < 64 by omega, show 40 + (i - 40) = i by omega, show i < 56 by omega]
  by_cases h7 : i < 56
  · simp [h1, h2, h3, h4, h5, h6, h7, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega, show ¬ i - 40 < 8 by omega,
      show i - 48 < 8 by omega, show i - 48 < 64 by omega, show 48 + (i - 48) = i by omega]
  · simp [h1, h2, h3, h4, h5, h6, h7, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega, show ¬ i - 40 < 8 by omega,
      show ¬ i - 48 < 8 by omega, show i - 56 < 8 by omega, show i - 56 < 64 by omega,
      show 56 + (i - 56) = i by omega]

/-- Shifting left by 24 keeps only the low byte. -/
theorem shl24_eq_lowByte (s : UInt32) : s <<< 24 = s.toUInt8.toUInt32 <<< 24 := by
  rw [← UInt32.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hl : (s <<< 24).toBitVec = s.toBitVec <<< 24 := by simp
  have hlow : s.toUInt8.toUInt32.toBitVec = (s.toBitVec.setWidth 8).setWidth 32 := by
    have hc : ∀ c : UInt8, c.toUInt32.toBitVec = c.toBitVec.setWidth 32 := fun _ => by simp
    have hs : s.toUInt8.toBitVec = s.toBitVec.setWidth 8 := by simp
    rw [hc, hs]
  have hr : (s.toUInt8.toUInt32 <<< 24).toBitVec = (s.toBitVec.setWidth 8).setWidth 32 <<< 24 := by
    rw [UInt32.toBitVec_shiftLeft, hlow]; simp
  simp only [hl, hr, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  by_cases h24 : i < 24
  · simp [h24]
  · simp [h24, show i - 24 < 8 by omega, show i - 24 < 32 by omega]

end Crc32c
