/-
Proof that the hardware-CRC path (`MemcpyCrc32c.Impl.Hw`) equals the bitwise
reference: `fast_eq_ref` for the three-stream CRC32C-instruction kernel.

Kernel-only proofs. They are about the Lean models of the instructions; that
the CPU agrees with the models is the trusted part (`SimdModels.Trusted`).
-/
import MemcpyCrc32c.Hw
import MemcpyCrc32c.Impl.Hw

namespace Crc32c
open Polynomial

theorem rawExtendPortableCold_eq (s : UInt32) (a : ByteArray) (off len : Nat)
    (h : off + len ≤ a.size) :
    rawExtendPortableCold s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendPortableCold
  by_cases hs : a.size < USize.size
  · have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    simp only [hs, ↓reduceDIte, rawExtendPortableUSize_eq, ho, hl]
  · simp only [hs, ↓reduceDIte, bytes_extract]

theorem hwBytes_eq (a : ByteArray) (hs : a.size < USize.size) (stop : USize)
    (hstop : stop.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (s : UInt32), stop.toNat - i.toNat = k →
      hwBytes a i stop hstop s = rawExtend s (bytes a i.toNat stop.toNat) := by
  intro k
  induction k with
  | zero =>
    intro i s hk
    have hn : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    rw [hwBytes]
    simp only [hn, ↓reduceDIte]
    rw [bytes_of_le a (by omega)]
    rfl
  | succ k ih =>
    intro i s hk
    have hlt : i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
    rw [hwBytes]
    simp only [hlt, ↓reduceDIte]
    rw [crc32c_u8_eq, ih _ _ (by omega), h1, bytes_cons a i.toNat stop.toNat (by omega) hstop]
    rfl

theorem hwLoop_eq (a : ByteArray) (hs : a.size < USize.size) (fin : USize)
    (hfin : fin.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ fin.toNat) (s : UInt32), fin.toNat - i.toNat = k →
      hwLoop a hs i fin hi hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi s hk
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have e8 : (8 : USize).toNat = 8 := by simp
    rw [hwLoop]
    by_cases h : 8 ≤ fin - i
    · have h' : 8 ≤ fin.toNat - i.toNat := by
        have := USize.le_iff_toNat_le.mp h
        rw [hsub, e8] at this; exact this
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      simp only [h, ↓reduceDIte]
      rw [ih (fin.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) _ rfl, crc32c_u64_eq, h8]
      obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 8 + m := ⟨fin.toNat - i.toNat - 8, by omega⟩
      rw [hm, rawExtend_load a i hs m (by omega)]
    · simp only [h, ↓reduceDIte]
      rw [hwBytes_eq a hs fin hfin _ _ _ rfl]

/-- The combining step, as a function of the three stream states. -/
def combine3 (L : USize) (s0 s1 s2 : UInt32) : UInt32 :=
  mulMod (mulMod s0 (powModU64 x64 0x80000000 (L / 8).toUInt64) ^^^ s1)
    (powModU64 x64 0x80000000 (L / 8).toUInt64) ^^^ s2

/-- Loop invariant of `hwFold3`: each stream state is the reference over the
bytes its stream has left, and the three are combined at the end. -/
theorem hwFold3_spec (a : ByteArray) (hs : a.size < USize.size) (stop L L2 : USize)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
      (s0 s1 s2 : UInt32), stop.toNat - i.toNat = k →
      hwFold3 a hs i stop L L2 hi hal hL2 hL s0 s1 s2 =
        combine3 L (rawExtend s0 (bytes a i.toNat stop.toNat))
          (rawExtend s1 (bytes a (i.toNat + L.toNat) (stop.toNat + L.toNat)))
          (rawExtend s2 (bytes a (i.toNat + 2 * L.toNat) (stop.toNat + 2 * L.toNat))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal s0 s1 s2 hk
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    rw [hwFold3]
    by_cases hlt : i < stop
    · have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
      have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
      have hi1 : (i + L).toNat = i.toNat + L.toNat := by
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
        rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hlt, ↓reduceDIte]
      rw [ih (stop.toNat - (i + 8).toNat) (by omega) (i + 8) (by omega) (by omega) _ _ _ rfl]
      obtain ⟨m, hm⟩ : ∃ m, stop.toNat = i.toNat + 8 + m := ⟨stop.toNat - i.toNat - 8, by omega⟩
      have r0 := rawExtend_load a i hs m (by omega) s0
      have r1 := rawExtend_load a (i + L) hs m (by omega) s1
      have r2 := rawExtend_load a (i + L2) hs m (by omega) s2
      simp only [hi1] at r1
      simp only [hi2] at r2
      have e1 : i.toNat + 8 + L.toNat = i.toNat + L.toNat + 8 := by omega
      have e2 : i.toNat + 8 + 2 * L.toNat = i.toNat + 2 * L.toNat + 8 := by omega
      have e3 : i.toNat + 8 + m + L.toNat = i.toNat + L.toNat + 8 + m := by omega
      have e4 : i.toNat + 8 + m + 2 * L.toNat = i.toNat + 2 * L.toNat + 8 + m := by omega
      simp only [crc32c_u64_eq, h8, hm, e1, e2, e3, e4]
      rw [r0, r1, r2]
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      simp only [hlt, ↓reduceDIte, heq]
      rw [bytes_of_le a (Nat.le_refl _), bytes_of_le a (Nat.le_refl _), bytes_of_le a (Nat.le_refl _)]
      rfl

/-- Three stream CRCs of `L` bytes each combine into the CRC of their concatenation. -/
theorem combine3_eq (s : UInt32) (L : USize) (hLm : L.toNat % 8 = 0) (A B C : List UInt8)
    (hA : A.length = L.toNat) (hB : B.length = L.toNat) (hC : C.length = L.toNat) :
    combine3 L (rawExtend s A) (rawExtend 0 B) (rawExtend 0 C) = rawExtend s (A ++ B ++ C) := by
  apply eq_of_π_P
  have e8 : (8 : USize).toNat = 8 := by simp
  have hf : π (P (powModU64 x64 0x80000000 (L / 8).toUInt64)) = π X ^ (8 * L.toNat) := by
    rw [powModU64_eq_go, π_P_powMod_go, P_one, π_P_x64, usize_toUInt64_toNat, USize.toNat_div, e8,
      ← pow_mul, map_one, one_mul]
    congr 1; omega
  simp only [combine3, P_xor, map_add, π_P_mulMod, hf, π_P_rawExtend, msgPoly_append,
    List.length_append, hA, hB, hC, P_zero, map_zero, zero_mul, zero_add, map_mul, map_pow]
  ring

theorem rawExtendHwUSize_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) :
    rawExtendHwUSize s a hs uoff ulen h =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendHwUSize
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h3 : 4096 ≤ ulen
  · have e4096 : (4096 : USize).toNat = 4096 := by simp
    have h3' : 4096 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h3; omega
    have e24 : (24 : USize).toNat = 24 := by simp
    have e8 : (8 : USize).toNat = 8 := by simp
    have e3 : (3 : USize).toNat = 3 := by simp
    have e2 : (2 : USize).toNat = 2 := by simp
    have hws : (ulen / 24).toNat = ulen.toNat / 24 := by rw [USize.toNat_div, e24]
    have hL : (ulen / 24 * 8).toNat = ulen.toNat / 24 * 8 := by
      rw [USize.toNat_mul, hws, e8]; exact Nat.mod_eq_of_lt (by omega)
    have hL2 : (2 * (ulen / 24 * 8)).toNat = 2 * (ulen / 24 * 8).toNat := by
      rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
    have hL3 : (3 * (ulen / 24 * 8)).toNat = 3 * (ulen / 24 * 8).toNat := by
      rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
    have hstop : (uoff + ulen / 24 * 8).toNat = uoff.toNat + (ulen / 24 * 8).toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have htail : (uoff + 3 * (ulen / 24 * 8)).toNat = uoff.toNat + 3 * (ulen / 24 * 8).toNat := by
      rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
    simp only [h3, ↓reduceDIte]
    rw [hwLoop_eq a hs _ (by omega) _ _ _ _ rfl,
      hwFold3_spec a hs _ (ulen / 24 * 8) _ hL2 (by omega) _ uoff (by omega) (by omega) _ _ _ rfl,
      htail, hfin, hstop]
    have lenA : (bytes a uoff.toNat (uoff.toNat + (ulen / 24 * 8).toNat)).length = (ulen / 24 * 8).toNat := by
      rw [length_bytes a _ _ (by omega)]; omega
    have lenB : (bytes a (uoff.toNat + (ulen / 24 * 8).toNat) (uoff.toNat + (ulen / 24 * 8).toNat + (ulen / 24 * 8).toNat)).length = (ulen / 24 * 8).toNat := by
      rw [length_bytes a _ _ (by omega)]; omega
    have lenC : (bytes a (uoff.toNat + 2 * (ulen / 24 * 8).toNat) (uoff.toNat + (ulen / 24 * 8).toNat + 2 * (ulen / 24 * 8).toNat)).length
        = (ulen / 24 * 8).toNat := by
      rw [length_bytes a _ _ (by omega)]; omega
    rw [combine3_eq s (ulen / 24 * 8) (by omega) _ _ _ lenA lenB lenC, ← rawExtend_append]
    have j1 : uoff.toNat + (ulen / 24 * 8).toNat + (ulen / 24 * 8).toNat = uoff.toNat + 2 * (ulen / 24 * 8).toNat := by omega
    have j2 : uoff.toNat + (ulen / 24 * 8).toNat + 2 * (ulen / 24 * 8).toNat = uoff.toNat + 3 * (ulen / 24 * 8).toNat := by omega
    rw [j1, j2,
      bytes_append a (i := uoff.toNat) (m := uoff.toNat + (ulen / 24 * 8).toNat) (j := uoff.toNat + 2 * (ulen / 24 * 8).toNat)
        (by omega) (by omega) (by omega),
      bytes_append a (i := uoff.toNat) (m := uoff.toNat + 2 * (ulen / 24 * 8).toNat) (j := uoff.toNat + 3 * (ulen / 24 * 8).toNat)
        (by omega) (by omega) (by omega),
      bytes_append a (i := uoff.toNat) (m := uoff.toNat + 3 * (ulen / 24 * 8).toNat)
        (j := uoff.toNat + ulen.toNat) (by omega) (by omega) (by omega)]
  · simp only [h3, ↓reduceDIte]
    rw [hwLoop_eq a hs _ (by omega) _ _ _ _ rfl, hfin]

/-- The hardware-CRC path computes the reference update on any in-bounds range. -/
theorem rawExtendHw_eq (s : UInt32) (a : ByteArray) (off len : Nat) (h : off + len ≤ a.size) :
    rawExtendHw s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendHw
  by_cases hsmall : a.size ≤ 0x7FFFFFFF
  · have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    simp only [hsmall, ↓reduceDIte, rawExtendHwUSize_eq, ho, hl]
  · simp only [hsmall, ↓reduceDIte, rawExtendPortableCold_eq]

/-- `fast_eq_ref`, hardware-CRC path: equal to the bitwise reference on every input. -/
theorem extendHw_eq_extend (c : UInt32) (a : ByteArray) : extendHw c a = extend c a := by
  simp [extendHw, extend, rawExtendHw_eq, bytes_whole]

/-- The hardware-CRC path satisfies the polynomial spec. -/
theorem extendHw_eq_spec (c : UInt32) (a : ByteArray) : extendHw c a = Spec.extend c a := by
  rw [extendHw_eq_extend, extend_eq_spec]

end Crc32c
