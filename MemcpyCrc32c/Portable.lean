/-
Proof that the portable path (`MemcpyCrc32c.Impl.Portable`) equals the bitwise
reference: `fast_eq_ref` for the portable kernel.

Depends on `Lean.ofReduceBool` through the two quarantined word identities in
`MemcpyCrc32c.BvDecide.Word64`.
-/
import MemcpyCrc32c.ZeroPoly
import MemcpyCrc32c.PolyShift
import MemcpyCrc32c.Impl.Portable
import MemcpyCrc32c.BvDecide.Word64

namespace Crc32c
open Polynomial

/-! ### Byte ranges of a `ByteArray` as lists -/

/-- The bytes `a[i, j)`. -/
def bytes (a : ByteArray) (i j : Nat) : List UInt8 := (a.data.toList.drop i).take (j - i)

theorem bytes_of_le (a : ByteArray) {i j : Nat} (h : j ≤ i) : bytes a i j = [] := by
  simp [bytes, Nat.sub_eq_zero_of_le h]

theorem bytes_cons (a : ByteArray) (i j : Nat) (hij : i < j) (hj : j ≤ a.size) :
    bytes a i j = a[i]'(by omega) :: bytes a (i + 1) j := by
  unfold bytes
  have hl : i < a.data.toList.length := by simp [ByteArray.size_data]; omega
  rw [List.drop_eq_getElem_cons hl, show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]
  simp
  rfl

theorem length_bytes (a : ByteArray) (i j : Nat) (hj : j ≤ a.size) :
    (bytes a i j).length = j - i := by
  simp [bytes, ByteArray.size_data]; omega

theorem bytes_whole (a : ByteArray) : bytes a 0 a.size = a.data.toList := by
  simp [bytes, ByteArray.size_data]

theorem bytes_extract (a : ByteArray) (i j : Nat) :
    (a.extract i j).data.toList = bytes a i j := by
  simp [bytes, ByteArray.data_extract]

/-! ### The bytewise loop -/

theorem bytesLoop_eq (a : ByteArray) (hs : a.size < USize.size) (stop : USize)
    (hstop : stop.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (s : UInt32), stop.toNat - i.toNat = k →
      bytesLoop a i stop hstop s = rawExtend s (bytes a i.toNat stop.toNat) := by
  intro k
  induction k with
  | zero =>
    intro i s hk
    have hn : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    rw [bytesLoop]
    simp only [hn, ↓reduceDIte]
    rw [bytes_of_le a (by omega)]
    rfl
  | succ k ih =>
    intro i s hk
    have hlt : i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
    rw [bytesLoop]
    simp only [hlt, ↓reduceDIte]
    rw [ih _ _ (by omega), h1, bytes_cons a i.toNat stop.toNat (by omega) hstop]
    rfl

/-! ### 64-bit words -/

/-- Reflected view of a 64-bit word, as a residue modulo `G`. -/
noncomputable abbrev R (x : UInt64) : Q := π (polyR x.toBitVec)

theorem R_xor (a b : UInt64) : R (a ^^^ b) = R a + R b := by
  simp [R, polyR_xor]

theorem R_zero : R 0 = 0 := by
  show π (polyR (0 : UInt64).toBitVec) = 0
  rw [show polyR (0 : UInt64).toBitVec = 0 from polyR_zero, map_zero]

theorem polyR_word64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    polyR (word64 b0 b1 b2 b3 b4 b5 b6 b7).toBitVec = msgPoly [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [BvDecide.word64_eq_xor]
  simp only [UInt64.toBitVec_xor, polyR_xor]
  simp [msgPoly, polyR_setWidth (show 8 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 8 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 16 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 24 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 32 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 40 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 48 ≤ 64 by omega),
    polyR_setWidth_shiftLeft (show 8 + 56 ≤ 64 by omega)]
  ring

theorem uget_eq (a : ByteArray) (j : USize) (n : Nat) (hj : j.toNat = n) (h : j.toNat < a.size) :
    a.uget j h = a[n]'(hj ▸ h) := by
  subst hj; rfl

theorem msgPoly_bytes_load (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 8 + m ≤ a.size) :
    msgPoly (bytes a i.toNat (i.toNat + 8 + m)) =
      polyR (load64 a i hs (by omega)).toBitVec * X ^ (8 * m) +
        msgPoly (bytes a (i.toNat + 8) (i.toNat + 8 + m)) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := usize_add_toNat i 7 (by omega)
  have hl : load64 a i hs (by omega) =
      word64 (a[i.toNat]'(by omega)) (a[i.toNat + 1]'(by omega)) (a[i.toNat + 2]'(by omega))
        (a[i.toNat + 3]'(by omega)) (a[i.toNat + 4]'(by omega)) (a[i.toNat + 5]'(by omega))
        (a[i.toNat + 6]'(by omega)) (a[i.toNat + 7]'(by omega)) := by
    show word64 (a.uget i _) (a.uget (i + 1) _) (a.uget (i + 2) _) (a.uget (i + 3) _)
      (a.uget (i + 4) _) (a.uget (i + 5) _) (a.uget (i + 6) _) (a.uget (i + 7) _) = _
    rw [uget_eq a i _ rfl, uget_eq a (i + 1) _ h1, uget_eq a (i + 2) _ h2, uget_eq a (i + 3) _ h3,
      uget_eq a (i + 4) _ h4, uget_eq a (i + 5) _ h5, uget_eq a (i + 6) _ h6, uget_eq a (i + 7) _ h7]
  rw [hl, polyR_word64]
  rw [bytes_cons a i.toNat _ (by omega) h, bytes_cons a (i.toNat + 1) _ (by omega) h,
    bytes_cons a (i.toNat + 2) _ (by omega) h, bytes_cons a (i.toNat + 3) _ (by omega) h,
    bytes_cons a (i.toNat + 4) _ (by omega) h, bytes_cons a (i.toNat + 5) _ (by omega) h,
    bytes_cons a (i.toNat + 6) _ (by omega) h, bytes_cons a (i.toNat + 7) _ (by omega) h]
  have hlen := length_bytes a (i.toNat + 8) (i.toNat + 8 + m) h
  simp only [msgPoly, List.length_cons, hlen]
  simp
  ring

theorem π_P_stepWord (s : UInt32) (w : UInt64) :
    π (P (stepWord s w)) = π (P s) * π X ^ 64 + R w * π X ^ 32 := by
  have h : stepWord s w = rawExtend s [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
      (w >>> 24).toUInt8, (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8,
      (w >>> 56).toUInt8] := rfl
  rw [h, π_P_rawExtend, ← polyR_word64, BvDecide.word64_bytes]
  simp

/-! ### The reduction step -/

theorem R_shift (v : UInt64) (r : Nat) (hr : r ≤ 64) (x y : UInt64)
    (hx : x.toBitVec = v.toBitVec <<< r) (hy : y.toBitVec = v.toBitVec >>> (64 - r)) :
    R x * π X ^ 64 + R y = R v * π X ^ (64 - r) := by
  have := congrArg π (polyR_shiftLeft_add_shiftRight v.toBitVec r hr)
  simpa [R, hx, hy] using this

theorem π_zero6_209 : π X ^ 209 + π X ^ 144 + π X ^ 54 + π X ^ 39 + π X ^ 14 + 1 = 0 := by
  have := AdjoinRoot.mk_eq_zero.mpr zero6_209
  simpa [π] using this

/-- One word `v`, four words ahead of the window, is congruent to its five
shifted copies inside the window: this is `v · X^47 · Z ≡ 0`. -/
theorem R_window (v : UInt64) :
    R v * π X ^ 256 =
      R (v <<< 1) * π X ^ 192 +
      (R (v >>> 63) + R (v <<< 27) + R (v <<< 42)) * π X ^ 128 +
      (R (v >>> 37) + R (v >>> 22) + R (v <<< 3) + R (v <<< 17)) * π X ^ 64 +
      (R (v >>> 61) + R (v >>> 47)) := by
  have A1 := R_shift v 1 (by omega) (v <<< 1) (v >>> 63) (by simp) (by simp)
  have A2 := R_shift v 27 (by omega) (v <<< 27) (v >>> 37) (by simp) (by simp)
  have A3 := R_shift v 42 (by omega) (v <<< 42) (v >>> 22) (by simp) (by simp)
  have A4 := R_shift v 3 (by omega) (v <<< 3) (v >>> 61) (by simp) (by simp)
  have A5 := R_shift v 17 (by omega) (v <<< 17) (v >>> 47) (by simp) (by simp)
  have hZ := π_zero6_209
  have h2 := Q_add_self (R v * (π X ^ 191 + π X ^ 101 + π X ^ 86 + π X ^ 61 + π X ^ 47))
  norm_num at A1 A2 A3 A4 A5
  linear_combination (-(π X ^ 128)) * A1 - π X ^ 64 * A2 - π X ^ 64 * A3 - A4 - A5 +
    R v * π X ^ 47 * hZ - h2

/-- The four pending words as a residue, most significant first. -/
noncomputable def W (n1 n2 n3 n4 : UInt64) : Q :=
  R n1 * π X ^ 192 + R n2 * π X ^ 128 + R n3 * π X ^ 64 + R n4

/-! ### The reduction loop -/

/-- Loop invariant of `fold209`: the pending words, placed at byte offset `i`,
plus the message from `i` on, determine the result. -/
theorem fold209_spec (a : ByteArray) (hs : a.size < USize.size) (stop fin : USize)
    (hstop : stop.toNat + 32 ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
      (n1 n2 n3 n4 : UInt64), stop.toNat - i.toNat = k →
      π (P (fold209 a hs i stop fin hi hal hstop hfin n1 n2 n3 n4)) =
        (W n1 n2 n3 n4 * π X ^ (8 * (fin.toNat - i.toNat - 32)) +
          π (msgPoly (bytes a i.toNat fin.toNat))) * π X ^ 32 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal n1 n2 n3 n4 hk
    rw [fold209]
    by_cases hlt : i < stop
    · have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      simp only [hlt, ↓reduceDIte]
      rw [ih (stop.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) (by omega) _ _ _ _ rfl]
      obtain ⟨D, hD⟩ : ∃ D, fin.toNat = i.toNat + 8 + (32 + D) := ⟨fin.toNat - i.toNat - 40, by omega⟩
      have hm := msgPoly_bytes_load a i hs (32 + D) (by omega)
      generalize load64 a i hs _ = ld at hm ⊢
      have hw := R_window (ld ^^^ n1)
      rw [R_xor] at hw
      have e1 : fin.toNat - (i + 8).toNat - 32 = D := by omega
      have e2 : fin.toNat - i.toNat - 32 = D + 8 := by omega
      rw [e1, e2, h8, hD, hm]
      simp only [W, R_xor, map_add, map_mul, map_pow]
      linear_combination (-(π X ^ (8 * D) * π X ^ 32)) * hw
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      have h8 : (stop + 8).toNat = stop.toNat + 8 := usize_add_toNat stop 8 (by omega)
      have h16 : (stop + 16).toNat = stop.toNat + 16 := usize_add_toNat stop 16 (by omega)
      have h24 : (stop + 24).toNat = stop.toNat + 24 := usize_add_toNat stop 24 (by omega)
      have h32 : (stop + 32).toNat = stop.toNat + 32 := usize_add_toNat stop 32 (by omega)
      simp only [hlt, ↓reduceDIte]
      obtain ⟨T, hT⟩ : ∃ T, fin.toNat = stop.toNat + 32 + T := ⟨fin.toNat - stop.toNat - 32, by omega⟩
      have m0 := msgPoly_bytes_load a stop hs (24 + T) (by omega)
      have m1 := msgPoly_bytes_load a (stop + 8) hs (16 + T) (by omega)
      have m2 := msgPoly_bytes_load a (stop + 16) hs (8 + T) (by omega)
      have m3 := msgPoly_bytes_load a (stop + 24) hs T (by omega)
      have f0 : stop.toNat + 8 + (24 + T) = fin.toNat := by omega
      have f1 : stop.toNat + 16 + (16 + T) = fin.toNat := by omega
      have f2 : stop.toNat + 24 + (8 + T) = fin.toNat := by omega
      have f3 : stop.toNat + 32 + T = fin.toNat := by omega
      have g1 : stop.toNat + 8 + 8 = stop.toNat + 16 := by omega
      have g2 : stop.toNat + 16 + 8 = stop.toNat + 24 := by omega
      have g3 : stop.toNat + 24 + 8 = stop.toNat + 32 := by omega
      simp only [f0] at m0
      simp only [h8, g1, f1] at m1
      simp only [h16, g2, f2] at m2
      simp only [h24, g3, f3] at m3
      have hlen := length_bytes a (stop.toNat + 32) fin.toNat hfin
      have eT : fin.toNat - stop.toNat - 32 = T := by omega
      have eL : fin.toNat - (stop.toNat + 32) = T := by omega
      rw [bytesLoop_eq a hs fin hfin _ _ _ rfl, π_P_rawExtend, h32, hlen]
      simp only [π_P_stepWord, P_zero, map_zero, zero_mul, zero_add, R_xor, heq, eT, eL]
      rw [m0, m1, m2, m3]
      simp only [W, map_add, map_mul, map_pow]
      ring

/-! ### `fast_eq_ref` for the portable path -/

theorem polyR_toUInt64 (s : UInt32) : polyR s.toUInt64.toBitVec = P s * X ^ 32 := by
  have : s.toUInt64.toBitVec = s.toBitVec.setWidth 64 := by simp
  rw [this, polyR_setWidth (by omega)]

/-- The portable path computes the reference update on any in-bounds range. -/
theorem rawExtendPortable_eq (s : UInt32) (a : ByteArray) (off len : Nat)
    (h : off + len ≤ a.size) :
    rawExtendPortable s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendPortable
  by_cases hs : a.size < USize.size
  · simp only [hs, ↓reduceDIte]
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hf : (off + len).toUSize.toNat = off + len := USize.toNat_ofNat_of_lt' (by omega)
    by_cases h40 : 40 ≤ len
    · simp only [h40, ↓reduceDIte]
      apply eq_of_π_P
      rw [fold209_spec a hs _ _ _ _ _ _ _ _ _ _ _ _ rfl, π_P_rawExtend, ho, hf,
        length_bytes a off (off + len) h]
      have e : off + len - off - 32 = len - 32 := by omega
      have e' : off + len - off = 32 + (len - 32) := by omega
      rw [e, e']
      simp only [W, R, R_zero, polyR_toUInt64, map_mul, map_pow, zero_mul, add_zero]
      ring
    · simp only [h40, ↓reduceDIte]
      rw [bytesLoop_eq a hs _ _ _ _ _ rfl, ho, hf]
  · simp only [hs, ↓reduceDIte, bytes_extract]

/-- `fast_eq_ref`, portable path: equal to the bitwise reference on every input. -/
theorem extendPortable_eq_extend (c : UInt32) (a : ByteArray) : extendPortable c a = extend c a := by
  simp [extendPortable, extend, rawExtendPortable_eq, bytes_whole]

/-- The portable path satisfies the polynomial spec. -/
theorem extendPortable_eq_spec (c : UInt32) (a : ByteArray) :
    extendPortable c a = Spec.extend c a := by
  rw [extendPortable_eq_extend, extend_eq_spec]

end Crc32c
