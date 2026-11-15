/-
Proof that the portable path (`MemcpyCrc32c.Impl.Portable`) equals the bitwise
reference: `fast_eq_ref` for the portable kernel. Kernel-only proofs (no
`bv_decide` or extra axioms).
-/
import MemcpyCrc32c.ZeroPoly
import MemcpyCrc32c.PolyShift
import MemcpyCrc32c.Impl.Portable
import MemcpyCrc32c.Word64

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

theorem bytes_append (a : ByteArray) {i m j : Nat} (him : i ≤ m) (hmj : m ≤ j) (hj : j ≤ a.size) :
    bytes a i m ++ bytes a m j = bytes a i j := by
  obtain ⟨k, hk⟩ : ∃ k, m - i = k := ⟨_, rfl⟩
  induction k generalizing i with
  | zero => rw [bytes_of_le a (by omega), show i = m by omega, List.nil_append]
  | succ k ih =>
    rw [bytes_cons a i m (by omega) (by omega), bytes_cons a i j (by omega) hj,
      List.cons_append, @ih (i + 1) (by omega) (by omega)]

theorem rawExtend_append (s : UInt32) (xs ys : List UInt8) :
    rawExtend s (xs ++ ys) = rawExtend (rawExtend s xs) ys := by
  simp [rawExtend]

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

theorem polyR_word16 (b0 b1 : UInt8) :
    polyR (word16 b0 b1).toBitVec = msgPoly [b0, b1] := by
  rw [word16_eq_xor]
  simp only [UInt16.toBitVec_xor, polyR_xor]
  simp [msgPoly, polyR_setWidth (show 8 ≤ 16 by omega),
    polyR_setWidth_shiftLeft (show 8 + 8 ≤ 16 by omega)]

theorem polyR_word32 (b0 b1 b2 b3 : UInt8) :
    polyR (word32 b0 b1 b2 b3).toBitVec = msgPoly [b0, b1, b2, b3] := by
  rw [word32_eq_xor]
  simp only [UInt32.toBitVec_xor, polyR_xor]
  simp [msgPoly, polyR_setWidth (show 8 ≤ 32 by omega),
    polyR_setWidth_shiftLeft (show 8 + 8 ≤ 32 by omega),
    polyR_setWidth_shiftLeft (show 8 + 16 ≤ 32 by omega),
    polyR_setWidth_shiftLeft (show 8 + 24 ≤ 32 by omega)]
  ring

theorem polyR_word64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    polyR (word64 b0 b1 b2 b3 b4 b5 b6 b7).toBitVec = msgPoly [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [word64_eq_xor]
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

theorem msgPoly_bytes_load16 (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 2 + m ≤ a.size) :
    msgPoly (bytes a i.toNat (i.toNat + 2 + m)) =
      polyR (load16 a i hs (by omega)).toBitVec * X ^ (8 * m) +
        msgPoly (bytes a (i.toNat + 2) (i.toNat + 2 + m)) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have hl : load16 a i hs (by omega) = word16 (a[i.toNat]'(by omega)) (a[i.toNat + 1]'(by omega)) := by
    show word16 (a.uget i _) (a.uget (i + 1) _) = _
    rw [uget_eq a i _ rfl, uget_eq a (i + 1) _ h1]
  rw [hl, polyR_word16, bytes_cons a i.toNat _ (by omega) h,
    bytes_cons a (i.toNat + 1) _ (by omega) h]
  have hlen := length_bytes a (i.toNat + 2) (i.toNat + 2 + m) h
  simp only [msgPoly, List.length_cons, hlen]
  simp
  ring

theorem msgPoly_bytes_load32 (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 4 + m ≤ a.size) :
    msgPoly (bytes a i.toNat (i.toNat + 4 + m)) =
      polyR (load32 a i hs (by omega)).toBitVec * X ^ (8 * m) +
        msgPoly (bytes a (i.toNat + 4) (i.toNat + 4 + m)) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  have hl : load32 a i hs (by omega) =
      word32 (a[i.toNat]'(by omega)) (a[i.toNat + 1]'(by omega))
        (a[i.toNat + 2]'(by omega)) (a[i.toNat + 3]'(by omega)) := by
    show word32 (a.uget i _) (a.uget (i + 1) _) (a.uget (i + 2) _) (a.uget (i + 3) _) = _
    rw [uget_eq a i _ rfl, uget_eq a (i + 1) _ h1, uget_eq a (i + 2) _ h2, uget_eq a (i + 3) _ h3]
  rw [hl, polyR_word32, bytes_cons a i.toNat _ (by omega) h,
    bytes_cons a (i.toNat + 1) _ (by omega) h, bytes_cons a (i.toNat + 2) _ (by omega) h,
    bytes_cons a (i.toNat + 3) _ (by omega) h]
  have hlen := length_bytes a (i.toNat + 4) (i.toNat + 4 + m) h
  simp only [msgPoly, List.length_cons, hlen]
  simp
  ring

theorem stepU16_eq_rawExtend (s : UInt32) (v : UInt16) :
    stepU16 s v = rawExtend s [v.toUInt8, (v >>> 8).toUInt8] := rfl

theorem stepU32_eq_rawExtend (s : UInt32) (v : UInt32) :
    stepU32 s v = rawExtend s [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8] := rfl

theorem π_P_stepU16 (s : UInt32) (v : UInt16) :
    π (P (stepU16 s v)) = π (P s) * π X ^ 16 + π (polyR v.toBitVec) * π X ^ 32 := by
  rw [stepU16_eq_rawExtend, π_P_rawExtend, ← polyR_word16, word16_bytes]
  simp

theorem π_P_stepU32 (s : UInt32) (v : UInt32) :
    π (P (stepU32 s v)) = π (P s) * π X ^ 32 + π (polyR v.toBitVec) * π X ^ 32 := by
  rw [stepU32_eq_rawExtend, π_P_rawExtend, ← polyR_word32, word32_bytes]
  simp

theorem π_P_stepWord (s : UInt32) (w : UInt64) :
    π (P (stepWord s w)) = π (P s) * π X ^ 64 + R w * π X ^ 32 := by
  have h : stepWord s w = rawExtend s [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
      (w >>> 24).toUInt8, (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8,
      (w >>> 56).toUInt8] := rfl
  rw [h, π_P_rawExtend, ← polyR_word64, word64_bytes]
  simp

/-! ### Table lookups -/

theorem polyR_toUInt64 (s : UInt32) : polyR s.toUInt64.toBitVec = P s * X ^ 32 := by
  have : s.toUInt64.toBitVec = s.toBitVec.setWidth 64 := by simp
  rw [this, polyR_setWidth (by omega)]

theorem sliceTableEntry_eq (m : Fin 8192) (k b r : Nat) (hb : b < 256) (hr : r < 4)
    (hm : m.val = k * 1024 + b * 4 + r) :
    sliceTableEntry m =
      (rawExtend 0 (UInt8.ofNat b :: List.replicate (7 - k) 0) >>> (r * 8).toUInt32).toUInt8 := by
  unfold sliceTableEntry
  rw [hm]
  have hd : (k * 1024 + b * 4 + r) / 4 = 256 * k + b := by omega
  have hmod : (k * 1024 + b * 4 + r) % 4 = r := by omega
  have e1 : (256 * k + b) % 256 = b := by omega
  have e2 : (256 * k + b) / 256 = k := by omega
  simp only [hd, hmod, e1, e2]

theorem tbl_eq (k : USize) (hk : k.toNat < 8) (b : UInt8) :
    tbl k hk b = rawExtend 0 (b :: List.replicate (7 - k.toNat) 0) := by
  have hs : 8192 < USize.size := by have := usize_size_gt; omega
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hblt := b.toNat_lt
  have hb : b.toUSize.toNat = b.toNat := by simp
  have h1024 : (1024 : USize).toNat = 1024 := by simp
  have h4 : (4 : USize).toNat = 4 := by simp
  have hm1 : (k * 1024).toNat = k.toNat * 1024 := by
    rw [USize.toNat_mul, h1024]; exact Nat.mod_eq_of_lt (by omega)
  have hm2 : (b.toUSize * 4).toNat = b.toNat * 4 := by
    rw [USize.toNat_mul, hb, h4]; exact Nat.mod_eq_of_lt (by omega)
  let base : USize := k * 1024 + b.toUSize * 4
  have hbase0 : base.toNat = k.toNat * 1024 + b.toNat * 4 := by
    show (k * 1024 + b.toUSize * 4).toNat = _
    rw [USize.toNat_add, hm1, hm2]; exact Nat.mod_eq_of_lt (by omega)
  have h0 : (k * 1024 + b.toUSize * 4).toNat = k.toNat * 1024 + b.toNat * 4 + 0 :=
    hbase0.trans (Nat.add_zero _).symm
  have h1 : (k * 1024 + b.toUSize * 4 + 1).toNat = k.toNat * 1024 + b.toNat * 4 + 1 :=
    (usize_add_toNat base 1 (by omega)).trans (by omega)
  have h2 : (k * 1024 + b.toUSize * 4 + 2).toNat = k.toNat * 1024 + b.toNat * 4 + 2 :=
    (usize_add_toNat base 2 (by omega)).trans (by omega)
  have h3 : (k * 1024 + b.toUSize * 4 + 3).toNat = k.toNat * 1024 + b.toNat * 4 + 3 :=
    (usize_add_toNat base 3 (by omega)).trans (by omega)
  unfold tbl
  dsimp only
  simp only [SimdModels.loadU8, SimdModels.Model.loadU8]
  rw [sliceTableBytes_uget, sliceTableBytes_uget, sliceTableBytes_uget, sliceTableBytes_uget,
    sliceTableEntry_eq _ k.toNat b.toNat 0 hblt (by omega) h0,
    sliceTableEntry_eq _ k.toNat b.toNat 1 hblt (by omega) h1,
    sliceTableEntry_eq _ k.toNat b.toNat 2 hblt (by omega) h2,
    sliceTableEntry_eq _ k.toNat b.toNat 3 hblt (by omega) h3]
  simp only [UInt8.ofNat_toNat]
  simpa using word32_bytes (rawExtend 0 (b :: List.replicate (7 - k.toNat) 0))

theorem π_P_tbl (k : USize) (hk : k.toNat < 8) (b : UInt8) :
    π (P (tbl k hk b)) = π (polyR b.toBitVec) * π X ^ (8 * (7 - k.toNat) + 32) := by
  rw [tbl_eq, π_P_rawExtend, P_zero]
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
  rw [e1, shl24_eq_lowByte, e2, e2', polyR_setWidth_shiftLeft (by omega), e3] at h
  simp only [Nat.reduceSub, pow_zero, mul_one] at h
  have h' := congrArg π h
  simp only [map_add, map_mul, map_pow] at h'
  have hx : polyR (s.toUInt8 ^^^ b).toBitVec = polyR s.toUInt8.toBitVec + polyR b.toBitVec := by
    simp [polyR_xor]
  have u7 : (7 : USize).toNat = 7 := by simp
  rw [π_P_stepByte, stepByteT, P_xor, map_add, π_P_tbl, u7, hx, map_add]
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  linear_combination h'

theorem stepWordT0_eq (w : UInt64) : stepWordT0 w = stepWord 0 w := by
  apply eq_of_π_P
  have hx : R w = π (msgPoly [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
      (w >>> 24).toUInt8, (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8,
      (w >>> 56).toUInt8]) := by
    rw [← polyR_word64, word64_bytes]
  simp only [msgPoly, List.length_cons, List.length_nil, map_add, map_mul, map_pow, map_zero] at hx
  have u0 : (0 : USize).toNat = 0 := by simp
  have u1 : (1 : USize).toNat = 1 := by simp
  have u2 : (2 : USize).toNat = 2 := by simp
  have u3 : (3 : USize).toNat = 3 := by simp
  have u4 : (4 : USize).toNat = 4 := by simp
  have u5 : (5 : USize).toNat = 5 := by simp
  have u6 : (6 : USize).toNat = 6 := by simp
  have u7 : (7 : USize).toNat = 7 := by simp
  rw [π_P_stepWord, P_zero, stepWordT0, stepWordT32, u64_lo32_byte0, u64_lo32_byte1,
    u64_lo32_byte2, u64_lo32_byte3, u64_hi32_byte0, u64_hi32_byte1, u64_hi32_byte2, u64_hi32_byte3]
  simp only [P_xor, map_add, π_P_tbl, u0, u1, u2, u3, u4, u5, u6, u7, map_zero, zero_mul, zero_add,
    Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  linear_combination (-(π X ^ 32)) * hx

theorem stepWordT_eq (s : UInt32) (w : UInt64) : stepWordT s w = stepWord s w := by
  have heq : stepWordT s w = stepWordT0 (w ^^^ s.toUInt64) := by
    simp only [stepWordT, stepWordT0, xor_toUInt64_lo32, xor_toUInt64_hi32]
  apply eq_of_π_P
  rw [heq, stepWordT0_eq, π_P_stepWord, π_P_stepWord, P_zero, R_xor]
  have hs : R s.toUInt64 = π (P s) * π X ^ 32 := by
    show π (polyR s.toUInt64.toBitVec) = _
    rw [polyR_toUInt64, map_mul, map_pow]
  rw [hs, map_zero]
  ring

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

theorem load32_pair_eq (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) (h4 : (i + 4).toNat = i.toNat + 4) (s : UInt32) :
    stepWordT32 (load32 a i hs (by omega) ^^^ s) (load32 a (i + 4) hs (by omega)) =
      stepWordT s (load64 a i hs h) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := usize_add_toNat i 7 (by omega)
  have h41 : ((i + 4) + 1).toNat = i.toNat + 5 :=
    (usize_add_toNat (i + 4) 1 (by omega)).trans (by omega)
  have h42 : ((i + 4) + 2).toNat = i.toNat + 6 :=
    (usize_add_toNat (i + 4) 2 (by omega)).trans (by omega)
  have h43 : ((i + 4) + 3).toNat = i.toNat + 7 :=
    (usize_add_toNat (i + 4) 3 (by omega)).trans (by omega)
  have hlo : load32 a i hs (by omega) = (load64 a i hs h).toUInt32 := by
    show word32 (a.uget i _) (a.uget (i + 1) _) (a.uget (i + 2) _) (a.uget (i + 3) _) =
      (word64 (a.uget i _) (a.uget (i + 1) _) (a.uget (i + 2) _) (a.uget (i + 3) _)
        (a.uget (i + 4) _) (a.uget (i + 5) _) (a.uget (i + 6) _) (a.uget (i + 7) _)).toUInt32
    rw [word64_toUInt32]
  have hhi : load32 a (i + 4) hs (by omega) = (load64 a i hs h >>> 32).toUInt32 := by
    show word32 (a.uget (i + 4) _) (a.uget ((i + 4) + 1) _) (a.uget ((i + 4) + 2) _)
        (a.uget ((i + 4) + 3) _) =
      (word64 (a.uget i _) (a.uget (i + 1) _) (a.uget (i + 2) _) (a.uget (i + 3) _)
        (a.uget (i + 4) _) (a.uget (i + 5) _) (a.uget (i + 6) _) (a.uget (i + 7) _) >>> 32).toUInt32
    rw [word64_hi_toUInt32, uget_eq a ((i + 4) + 1) _ h41, uget_eq a ((i + 4) + 2) _ h42,
      uget_eq a ((i + 4) + 3) _ h43, uget_eq a (i + 5) _ h5, uget_eq a (i + 6) _ h6,
      uget_eq a (i + 7) _ h7]
  rw [hlo, hhi]; rfl

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
      have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      simp only [h, ↓reduceDIte]
      rw [ih (fin.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) _ rfl,
        load32_pair_eq a i hs (by omega) h4 s, stepWordT_eq, h8]
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

/-! ### The reduction loops (1-stream and 4-stream) -/

/-- Stream invariant: pending 4-word window placed at byte offset `p` up to `fin`. -/
noncomputable def streamInv (a : ByteArray) (p fin : Nat) (n1 n2 n3 n4 : UInt64) : Q :=
  (W n1 n2 n3 n4 * π X ^ (8 * (fin - p - 32)) + π (msgPoly (bytes a p fin))) * π X ^ 32

theorem step209_inv (a : ByteArray) (hs : a.size < USize.size) (p : USize) (fin : Nat)
    (h : p.toNat + 40 ≤ fin) (hfin : fin ≤ a.size) (n1 n2 n3 n4 : UInt64) :
    streamInv a (p.toNat + 8) fin
      (next209_1 n2 (load64 a p hs (by omega) ^^^ n1))
      (next209_2 n3 (load64 a p hs (by omega) ^^^ n1))
      (next209_3 n4 (load64 a p hs (by omega) ^^^ n1))
      (next209_4 (load64 a p hs (by omega) ^^^ n1)) =
    streamInv a p.toNat fin n1 n2 n3 n4 := by
  unfold streamInv next209_1 next209_2 next209_3 next209_4
  obtain ⟨D, hD⟩ : ∃ D, fin = p.toNat + 8 + (32 + D) := ⟨fin - p.toNat - 40, by omega⟩
  have hm := msgPoly_bytes_load a p hs (32 + D) (by omega)
  generalize load64 a p hs _ = ld at hm ⊢
  have hw := R_window (ld ^^^ n1)
  rw [R_xor] at hw
  have e1 : fin - (p.toNat + 8) - 32 = D := by omega
  have e2 : fin - p.toNat - 32 = D + 8 := by omega
  rw [e1, e2, hD, hm]
  simp only [W, R_xor, map_add, map_mul, map_pow]
  linear_combination (-(π X ^ (8 * D) * π X ^ 32)) * hw

theorem finish209_spec (a : ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 32 ≤ a.size) (n1 n2 n3 n4 : UInt64) :
    π (P (finish209 a hs p hp n1 n2 n3 n4)) =
      streamInv a p.toNat (p.toNat + 32) n1 n2 n3 n4 := by
  have h8 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  have h16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have h24 : (p + 24).toNat = p.toNat + 24 := usize_add_toNat p 24 (by omega)
  have m0 := msgPoly_bytes_load a p hs 24 (by omega)
  have m1 := msgPoly_bytes_load a (p + 8) hs 16 (by omega)
  have m2 := msgPoly_bytes_load a (p + 16) hs 8 (by omega)
  have m3 := msgPoly_bytes_load a (p + 24) hs 0 (by omega)
  have f0 : p.toNat + 8 + 24 = p.toNat + 32 := by omega
  have f1 : p.toNat + 16 + 16 = p.toNat + 32 := by omega
  have f2 : p.toNat + 24 + 8 = p.toNat + 32 := by omega
  have g1 : p.toNat + 8 + 8 = p.toNat + 16 := by omega
  have g2 : p.toNat + 16 + 8 = p.toNat + 24 := by omega
  have g3 : p.toNat + 24 + 8 = p.toNat + 32 := by omega
  simp only [f0] at m0
  simp only [h8, g1, f1] at m1
  simp only [h16, g2, f2] at m2
  simp only [h24, g3, bytes_of_le a (le_refl _), msgPoly] at m3
  have esub : p.toNat + 32 - p.toNat - 32 = 0 := by omega
  unfold finish209 streamInv
  dsimp only
  simp only [stepWordT0_eq, stepWordT_eq, π_P_stepWord, P_zero, map_zero, zero_mul, zero_add,
    R_xor, esub, Nat.mul_zero, pow_zero, mul_one]
  rw [m0, m1, m2, m3]
  simp only [W, map_add, map_mul, map_pow, map_zero]
  ring

theorem finish209Out_spec (a : ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 32 ≤ a.size) (n1 n2 n3 n4 : UInt64) :
    π (P (finish209Out a hs p hp n1 n2 n3 n4)) =
      streamInv a p.toNat (p.toNat + 32) n1 n2 n3 n4 :=
  finish209_spec a hs p hp n1 n2 n3 n4

theorem π_P_x64 : π (P x64) = π X ^ 64 := by
  rw [x64, π_P_powMod, P_x8, map_pow, ← pow_mul]

/-- Loop invariant of `fold209`: the pending words, placed at byte offset `i`,
plus the message from `i` on, determine the result. -/
theorem fold209_spec (a : ByteArray) (hs : a.size < USize.size) (stop fin : USize)
    (hstop : stop.toNat + 32 ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
      (n1 n2 n3 n4 : UInt64), stop.toNat - i.toNat = k →
      π (P (fold209 a hs i stop fin hi hal hstop hfin n1 n2 n3 n4)) =
        streamInv a i.toNat fin.toNat n1 n2 n3 n4 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal n1 n2 n3 n4 hk
    rw [fold209]
    by_cases hlt : i < stop
    · have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      simp only [hlt, ↓reduceDIte]
      rw [ih (stop.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) (by omega) _ _ _ _ rfl,
        h8, step209_inv a hs i fin.toNat (by omega) hfin]
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      have h32 : (stop + 32).toNat = stop.toNat + 32 := usize_add_toNat stop 32 (by omega)
      simp only [hlt, ↓reduceDIte]
      obtain ⟨T, hT⟩ : ∃ T, fin.toNat = stop.toNat + 32 + T := ⟨fin.toNat - stop.toNat - 32, by omega⟩
      have hlen := length_bytes a (stop.toNat + 32) fin.toNat hfin
      have hb := bytes_append a (i := stop.toNat) (m := stop.toNat + 32) (j := fin.toNat)
        (by omega) (by omega) hfin
      have eT : fin.toNat - stop.toNat - 32 = T := by omega
      have eL : fin.toNat - (stop.toNat + 32) = T := by omega
      have esub0 : stop.toNat + 32 - stop.toNat - 32 = 0 := by omega
      rw [bytesLoop_eq a hs fin hfin _ _ _ rfl, π_P_rawExtend, h32, hlen, finish209_spec]
      unfold streamInv
      rw [heq, ← hb, msgPoly_append, length_bytes a (stop.toNat + 32) fin.toNat hfin,
        esub0, eT, eL]
      simp only [Nat.mul_zero, pow_zero, mul_one, map_add, map_mul, map_pow]
      ring

/-- Loop invariant of `fold209_4x`: all four stream invariants advance in lockstep. -/
theorem fold209_4x_spec (a : ByteArray) (hs : a.size < USize.size) (stop L L2 L3 : USize)
    (hLm : L.toNat % 8 = 0) (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL : stop.toNat + 3 * L.toNat + 32 ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : UInt64),
      stop.toNat - i.toNat = k →
      π (P (fold209_4x a hs i stop L L2 L3 hi hal hLm hL2 hL3 hL
          a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4)) =
        (((streamInv a i.toNat (stop.toNat + 32) a1 a2 a3 a4 * π X ^ (8 * L.toNat) +
            streamInv a (i.toNat + L.toNat) (stop.toNat + L.toNat + 32) b1 b2 b3 b4) *
              π X ^ (8 * L.toNat) +
            streamInv a (i.toNat + 2 * L.toNat) (stop.toNat + 2 * L.toNat + 32) c1 c2 c3 c4) *
              π X ^ (8 * L.toNat) +
            streamInv a (i.toNat + 3 * L.toNat) (stop.toNat + 3 * L.toNat + 32) d1 d2 d3 d4) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hk
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    rw [fold209_4x]
    by_cases hlt : i < stop
    · have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      have hi1 : (i + L).toNat = i.toNat + L.toNat := by
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
        rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
      have hi3 : (i + L3).toNat = i.toNat + 3 * L.toNat := by
        rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
      have sh1 : i.toNat + 8 + L.toNat = (i + L).toNat + 8 := by omega
      have sh2 : i.toNat + 8 + 2 * L.toNat = (i + L2).toNat + 8 := by omega
      have sh3 : i.toNat + 8 + 3 * L.toNat = (i + L3).toNat + 8 := by omega
      simp only [hlt, ↓reduceDIte]
      rw [ih (stop.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) (by omega)
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl]
      rw [h8, sh1, sh2, sh3,
        step209_inv a hs i (stop.toNat + 32) (by omega) (by omega),
        step209_inv a hs (i + L) (stop.toNat + L.toNat + 32) (by omega) (by omega),
        step209_inv a hs (i + L2) (stop.toNat + 2 * L.toNat + 32) (by omega) (by omega),
        step209_inv a hs (i + L3) (stop.toNat + 3 * L.toNat + 32) (by omega) (by omega),
        hi1, hi2, hi3]
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      have hs1 : (stop + L).toNat = stop.toNat + L.toNat := by
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hs2 : (stop + L2).toNat = stop.toNat + 2 * L.toNat := by
        rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
      have hs3 : (stop + L3).toNat = stop.toNat + 3 * L.toNat := by
        rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
      have e8 : (8 : USize).toNat = 8 := by simp
      have hmulFast (x y : UInt32) : π (P (mulModFast x y)) = π (P x) * π (P y) := by
        have hgo : mulModFast x y = mulMod.go 32 x y 0 := rfl
        rw [hgo, π_P_mulMod_go 32 x y 0 (fun j hj => by omega), P_zero]
        simp
      have hEntry (m : Fin 8196) (w r : Nat) (hr : r < 4) (hm : m.val = w * 4 + r) :
          x64ShiftEntry m = ((powMod x64 w) >>> (r * 8).toUInt32).toUInt8 := by
        unfold x64ShiftEntry; rw [hm]
        have hd : (w * 4 + r) / 4 = w := by omega
        have hmod : (w * 4 + r) % 4 = r := by omega
        simp only [hd, hmod]
      have hSmall (ws : USize) (hws : ws.toNat < 2049) :
          x64ShiftSmall ws hws = powMod x64 ws.toNat := by
        have hs8 : 8196 < USize.size := by have := usize_size_gt; omega
        have h4 : (4 : USize).toNat = 4 := by simp
        have hbase : (ws * 4).toNat = ws.toNat * 4 := by
          rw [USize.toNat_mul, h4]; exact Nat.mod_eq_of_lt (by omega)
        have r0 : (ws * 4).toNat = ws.toNat * 4 + 0 := hbase.trans (Nat.add_zero _).symm
        have r1 : (ws * 4 + 1).toNat = ws.toNat * 4 + 1 :=
          (usize_add_toNat (ws * 4) 1 (by omega)).trans (by omega)
        have r2 : (ws * 4 + 2).toNat = ws.toNat * 4 + 2 :=
          (usize_add_toNat (ws * 4) 2 (by omega)).trans (by omega)
        have r3 : (ws * 4 + 3).toNat = ws.toNat * 4 + 3 :=
          (usize_add_toNat (ws * 4) 3 (by omega)).trans (by omega)
        unfold x64ShiftSmall load32
        dsimp only
        simp only [SimdModels.loadU8, SimdModels.Model.loadU8]
        rw [x64ShiftBytes_uget, x64ShiftBytes_uget, x64ShiftBytes_uget, x64ShiftBytes_uget,
          hEntry _ ws.toNat 0 (by omega) r0,
          hEntry _ ws.toNat 1 (by omega) r1,
          hEntry _ ws.toNat 2 (by omega) r2,
          hEntry _ ws.toNat 3 (by omega) r3]
        simpa using word32_bytes (powMod x64 ws.toNat)
      have hf : π (P (x64ShiftWords (L / 8))) = π X ^ (8 * L.toNat) := by
        unfold x64ShiftWords
        by_cases hsm : L / 8 < 2049
        · have e2049 : (2049 : USize).toNat = 2049 := by simp
          have hlt2 : (L / 8).toNat < 2049 := by have := USize.lt_iff_toNat_lt.mp hsm; omega
          simp only [hsm, ↓reduceDIte, hSmall (L / 8) hlt2, USize.toNat_div, e8,
            π_P_powMod, π_P_x64, ← pow_mul, show 64 * (L.toNat / 8) = 8 * L.toNat by omega]
        · simp only [hsm, ↓reduceDIte, powModU64_eq_go, usize_toUInt64_toNat, USize.toNat_div, e8,
            π_P_powMod_go, P_one, map_one, one_mul, π_P_x64, ← pow_mul,
            show 64 * (L.toNat / 8) = 8 * L.toNat by omega]
      simp only [hlt, ↓reduceDIte, combine4x, P_xor, map_add, hmulFast, hf,
        finish209Out_spec, hs1, hs2, hs3, heq]
      ring

theorem fold209_4x_entry (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff stop L L2 L3 : USize)
    (hi : uoff.toNat ≤ stop.toNat) (hal : (stop.toNat - uoff.toNat) % 8 = 0)
    (hLm : L.toNat % 8 = 0) (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL : stop.toNat + 3 * L.toNat + 32 ≤ a.size)
    (hbody : stop.toNat + 32 = uoff.toNat + L.toNat) :
    fold209_4x a hs uoff stop L L2 L3 hi hal hLm hL2 hL3 hL
      s.toUInt64 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0 =
    rawExtend s (bytes a uoff.toNat (uoff.toNat + 4 * L.toNat)) := by
  apply eq_of_π_P
  rw [fold209_4x_spec a hs stop L L2 L3 hLm hL2 hL3 hL _ uoff hi hal
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl]
  let p0 := uoff.toNat
  have f1 : stop.toNat + 32 = p0 + L.toNat := hbody
  have f2 : stop.toNat + L.toNat + 32 = p0 + 2 * L.toNat := by omega
  have f3 : stop.toNat + 2 * L.toNat + 32 = p0 + 3 * L.toNat := by omega
  have f4 : stop.toNat + 3 * L.toNat + 32 = p0 + 4 * L.toNat := by omega
  have hS0 : streamInv a p0 (p0 + L.toNat) s.toUInt64 0 0 0 =
      π (P (rawExtend s (bytes a p0 (p0 + L.toNat)))) := by
    unfold streamInv
    obtain ⟨M, hM⟩ : ∃ M, L.toNat = 32 + M := ⟨L.toNat - 32, by omega⟩
    have esub : p0 + L.toNat - p0 - 32 = M := by omega
    have hlen : (bytes a p0 (p0 + L.toNat)).length = L.toNat := by
      rw [length_bytes a p0 (p0 + L.toNat) (by omega)]; omega
    rw [π_P_rawExtend, hlen, esub, hM]
    simp only [W, R, R_zero, polyR_toUInt64, map_mul, map_pow, zero_mul, add_zero,
      Nat.mul_add, pow_add]
    ring
  have hZero (x y : Nat) : streamInv a x y 0 0 0 0 = π (msgPoly (bytes a x y)) * π X ^ 32 := by
    simp [streamInv, W, R_zero]
  have step (u : UInt32) (x y : Nat) (hlen : (bytes a x y).length = L.toNat) :
      π (P u) * π X ^ (8 * L.toNat) + π (msgPoly (bytes a x y)) * π X ^ 32 =
        π (P (rawExtend u (bytes a x y))) := by
    rw [π_P_rawExtend, hlen]
  rw [f1, f2, f3, f4, hS0, hZero, hZero, hZero,
    step _ (p0 + L.toNat) (p0 + 2 * L.toNat) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (p0 + 2 * L.toNat) (p0 + 3 * L.toNat) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (p0 + 3 * L.toNat) (p0 + 4 * L.toNat) (by rw [length_bytes a _ _ (by omega)]; omega)]
  simp only [← rawExtend_append,
    bytes_append a (i := p0) (m := p0 + L.toNat) (j := p0 + 2 * L.toNat) (by omega) (by omega) (by omega),
    bytes_append a (i := p0) (m := p0 + 2 * L.toNat) (j := p0 + 3 * L.toNat) (by omega) (by omega) (by omega),
    bytes_append a (i := p0) (m := p0 + 3 * L.toNat) (j := p0 + 4 * L.toNat) (by omega) (by omega) (by omega)]
  rfl

/-! ### `fast_eq_ref` for the portable path -/

theorem rawExtendPortableUSize_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) :
    rawExtendPortableUSize s a hs uoff ulen h =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendPortableUSize
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h4x : 2048 ≤ ulen
  · have e2048 := usize_2048_toNat
    have h4x' : 2048 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h4x; omega
    have e32 : (32 : USize).toNat = 32 := by simp
    have e8 : (8 : USize).toNat = 8 := by simp
    have e4 : (4 : USize).toNat = 4 := by simp
    have e3 : (3 : USize).toNat = 3 := by simp
    have e2 : (2 : USize).toNat = 2 := by simp
    let ws := ulen / 32
    have hws : ws.toNat = ulen.toNat / 32 := by rw [USize.toNat_div, e32]
    let L := ws * 8
    have hL : L.toNat = ws.toNat * 8 := by
      rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
    let L2 := 2 * L
    have hL2 : L2.toNat = 2 * L.toNat := by
      rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
    let L3 := 3 * L
    have hL3 : L3.toNat = 3 * L.toNat := by
      rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
    let body := (ws - 4) * 8
    have hsub : (ws - 4).toNat = ws.toNat - 4 := by
      rw [USize.toNat_sub_of_le ws 4 (USize.le_iff_toNat_le.mpr (by omega)), e4]
    have hbody : body.toNat = (ws.toNat - 4) * 8 := by
      rw [USize.toNat_mul, hsub, e8]; exact Nat.mod_eq_of_lt (by omega)
    have hstop : (uoff + body).toNat = uoff.toNat + body.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    let L4 := 4 * L
    have hL4 : L4.toNat = 4 * L.toNat := by
      rw [USize.toNat_mul, e4]; exact Nat.mod_eq_of_lt (by omega)
    have htail : (uoff + L4).toNat = uoff.toNat + 4 * L.toNat := by
      rw [USize.toNat_add, hL4]; exact Nat.mod_eq_of_lt (by omega)
    simp only [h4x, ↓reduceDIte]
    rw [sliceLoop_eq a hs _ _ _ _ _ _ rfl,
      fold209_4x_entry s a hs uoff (uoff + body) L L2 L3 _ _ _ hL2 hL3 _ (by omega),
      htail, hfin, ← rawExtend_append, bytes_append a (by omega) (by omega) h]
  · simp only [h4x, ↓reduceDIte]
    by_cases h40 : 40 ≤ ulen
    · have e40 : (40 : USize).toNat = 40 := by simp
      have h40' : 40 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h40; omega
      simp only [h40, ↓reduceDIte]
      apply eq_of_π_P
      rw [fold209_spec a hs _ _ _ _ _ _ _ _ _ _ _ _ rfl, π_P_rawExtend, hfin,
        length_bytes a uoff.toNat (uoff.toNat + ulen.toNat) h]
      unfold streamInv
      have e : uoff.toNat + ulen.toNat - uoff.toNat - 32 = ulen.toNat - 32 := by omega
      have e' : uoff.toNat + ulen.toNat - uoff.toNat = 32 + (ulen.toNat - 32) := by omega
      rw [e, e']
      simp only [W, R, R_zero, polyR_toUInt64, map_mul, map_pow, zero_mul, add_zero]
      ring
    · simp only [h40, ↓reduceDIte]
      rw [sliceLoop_eq a hs _ _ _ _ _ _ rfl, hfin]

/-- The portable path computes the reference update on any in-bounds range. -/
theorem rawExtendPortable_eq (s : UInt32) (a : ByteArray) (off len : Nat)
    (h : off + len ≤ a.size) :
    rawExtendPortable s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendPortable rawExtendPortableCold
  by_cases hsmall : a.size ≤ 0x7FFFFFFF
  · have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    simp only [hsmall, ↓reduceDIte, rawExtendPortableUSize_eq, ho, hl]
  · simp only [hsmall, ↓reduceDIte]
    by_cases hs : a.size < USize.size
    · have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
      have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
      simp only [hs, ↓reduceDIte, rawExtendPortableUSize_eq, ho, hl]
    · simp only [hs, ↓reduceDIte, bytes_extract]

/-- `fast_eq_ref`, portable path: equal to the bitwise reference on every input. -/
theorem extendPortable_eq_extend (c : UInt32) (a : ByteArray) : extendPortable c a = extend c a := by
  simp [extendPortable, extend, rawExtendPortable_eq, bytes_whole]

/-- The portable path satisfies the polynomial spec. -/
theorem extendPortable_eq_spec (c : UInt32) (a : ByteArray) :
    extendPortable c a = Spec.extend c a := by
  rw [extendPortable_eq_extend, extend_eq_spec]

end Crc32c
