/-
Proof that the portable path (`MemcpyCrc32c.Impl.Portable`) equals the bitwise
reference: `fast_eq_ref` for the portable kernel.

Depends on the `bv_decide` axioms of the quarantined word identities in
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

/-! ### Table lookups -/

theorem polyR_toUInt64 (s : UInt32) : polyR s.toUInt64.toBitVec = P s * X ^ 32 := by
  have : s.toUInt64.toBitVec = s.toBitVec.setWidth 64 := by simp
  rw [this, polyR_setWidth (by omega)]

theorem π_P_tbl (j : Nat) (hj : j < 8) (b : UInt8) :
    π (P (tbl j hj b)) = π (polyR b.toBitVec) * π X ^ (8 * j + 32) := by
  have hb := b.toNat_lt
  have e1 : (256 * j + b.toNat) % 256 = b.toNat := by omega
  have e2 : (256 * j + b.toNat) / 256 = j := by omega
  have h : tbl j hj b = rawExtend 0 (b :: List.replicate j 0) := by
    simp only [tbl, sliceTable, Array.getElem_ofFn, e1, e2, UInt8.ofNat_toNat]
  rw [h, π_P_rawExtend, P_zero]
  simp only [msgPoly, msgPoly_replicate_zero, List.length_replicate, map_zero, zero_mul, zero_add,
    add_zero, map_mul, map_pow]
  ring

theorem stepByteT_eq (s : UInt32) (b : UInt8) : stepByteT s b = stepByte s b := by
  apply eq_of_π_P
  have h := polyR_shiftLeft_add_shiftRight s.toBitVec 24 (by omega)
  have e1 : s.toBitVec <<< 24 = (s <<< 24).toBitVec := by simp
  have e2 : ∀ x : UInt32, (x <<< 24).toBitVec = x.toBitVec <<< 24 := by intro x; simp
  have e2' : ∀ c : UInt8, c.toUInt32.toBitVec = c.toBitVec.setWidth 32 := by intro c; simp
  have e3 : s.toBitVec >>> (32 - 24) = (s >>> 8).toBitVec := by simp
  rw [e1, BvDecide.shl24_eq_lowByte, e2, e2', polyR_setWidth_shiftLeft (by omega), e3] at h
  simp only [Nat.reduceSub, pow_zero, mul_one] at h
  have h' := congrArg π h
  simp only [map_add, map_mul, map_pow] at h'
  have hx : polyR (s.toUInt8 ^^^ b).toBitVec = polyR s.toUInt8.toBitVec + polyR b.toBitVec := by
    simp [polyR_xor]
  rw [π_P_stepByte, stepByteT, P_xor, map_add, π_P_tbl, hx, map_add]
  linear_combination h'

theorem stepWordT_eq (s : UInt32) (w : UInt64) : stepWordT s w = stepWord s w := by
  apply eq_of_π_P
  have hx : R (w ^^^ s.toUInt64) = π (msgPoly [(w ^^^ s.toUInt64).toUInt8,
      ((w ^^^ s.toUInt64) >>> 8).toUInt8, ((w ^^^ s.toUInt64) >>> 16).toUInt8,
      ((w ^^^ s.toUInt64) >>> 24).toUInt8, ((w ^^^ s.toUInt64) >>> 32).toUInt8,
      ((w ^^^ s.toUInt64) >>> 40).toUInt8, ((w ^^^ s.toUInt64) >>> 48).toUInt8,
      ((w ^^^ s.toUInt64) >>> 56).toUInt8]) := by
    rw [← polyR_word64, BvDecide.word64_bytes]
  rw [R_xor] at hx
  have hs : R s.toUInt64 = π (P s) * π X ^ 32 := by
    show π (polyR s.toUInt64.toBitVec) = _
    rw [polyR_toUInt64, map_mul, map_pow]
  rw [hs] at hx
  simp only [msgPoly, List.length_cons, List.length_nil, map_add, map_mul, map_pow, map_zero] at hx
  rw [π_P_stepWord]
  simp only [stepWordT, P_xor, map_add, π_P_tbl]
  linear_combination (-(π X ^ 32)) * hx

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
    rw [stepByteT_eq, ih _ _ (by omega), h1, bytes_cons a i.toNat stop.toNat (by omega) hstop]
    rfl

/-! ### The short-input loop -/

theorem rawExtend_load (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 8 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a i.toNat (i.toNat + 8 + m)) =
      rawExtend (stepWord s (load64 a i hs (by omega))) (bytes a (i.toNat + 8) (i.toNat + 8 + m)) := by
  apply eq_of_π_P
  rw [π_P_rawExtend, π_P_rawExtend, π_P_stepWord, msgPoly_bytes_load a i hs m h,
    length_bytes a _ _ h, length_bytes a _ _ h]
  have e1 : i.toNat + 8 + m - i.toNat = 8 + m := by omega
  have e2 : i.toNat + 8 + m - (i.toNat + 8) = m := by omega
  rw [e1, e2]
  simp only [map_add, map_mul, map_pow]
  ring

theorem sliceLoop_eq (a : ByteArray) (hs : a.size < USize.size) (fin : USize)
    (hfin : fin.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ fin.toNat) (s : UInt32), fin.toNat - i.toNat = k →
      sliceLoop a hs i fin hi hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi s hk
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have e8 : (8 : USize).toNat = 8 := by simp
    rw [sliceLoop]
    by_cases h : 8 ≤ fin - i
    · have h' : 8 ≤ fin.toNat - i.toNat := by
        have := USize.le_iff_toNat_le.mp h
        rw [hsub, e8] at this; exact this
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      simp only [h, ↓reduceDIte]
      rw [ih (fin.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) _ rfl, stepWordT_eq, h8]
      obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 8 + m := ⟨fin.toNat - i.toNat - 8, by omega⟩
      rw [hm, rawExtend_load a i hs m (by omega)]
    · simp only [h, ↓reduceDIte]
      rw [bytesLoop_eq a hs fin hfin _ _ _ rfl]

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
      simp only [stepWordT_eq, π_P_stepWord, P_zero, map_zero, zero_mul, zero_add, R_xor, heq, eT, eL]
      rw [m0, m1, m2, m3]
      simp only [W, map_add, map_mul, map_pow]
      ring

/-! ### `fast_eq_ref` for the portable path -/

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
      rw [sliceLoop_eq a hs _ _ _ _ _ _ rfl, ho, hf]
  · simp only [hs, ↓reduceDIte, bytes_extract]

/-- `fast_eq_ref`, portable path: equal to the bitwise reference on every input. -/
theorem extendPortable_eq_extend (c : UInt32) (a : ByteArray) : extendPortable c a = extend c a := by
  simp [extendPortable, extend, rawExtendPortable_eq, bytes_whole]

/-- The portable path satisfies the polynomial spec. -/
theorem extendPortable_eq_spec (c : UInt32) (a : ByteArray) :
    extendPortable c a = Spec.extend c a := by
  rw [extendPortable_eq_extend, extend_eq_spec]

end Crc32c
