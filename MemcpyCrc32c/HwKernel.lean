/-
Proof that the hybrid hardware CRC32C + carry-less-multiply path
(`MemcpyCrc32c.Impl.Hw`) equals the bitwise reference (`fast_eq_ref`) and the
polynomial specification (`extendHw_eq_spec`).

Kernel-only proofs. They reason about the Lean models of the seven bindings
(`crc32c_u8/16/32/64`, `clmulLo`, `clmulHi`, `loadU64LE`); that the CPU agrees
with the models is the audited trust boundary (`SimdModels.Trusted`).
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

/-! ### Multi-byte load absorption lemmas -/

theorem rawExtend_load16 (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 2 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a i.toNat (i.toNat + 2 + m)) =
      rawExtend (stepU16 s (load16 a i hs (by omega))) (bytes a (i.toNat + 2) (i.toNat + 2 + m)) := by
  apply eq_of_π_P
  rw [π_P_rawExtend, π_P_rawExtend, π_P_stepU16, msgPoly_bytes_load16 a i hs m h,
    length_bytes a _ _ h, length_bytes a _ _ h]
  have e1 : i.toNat + 2 + m - i.toNat = 2 + m := by omega
  have e2 : i.toNat + 2 + m - (i.toNat + 2) = m := by omega
  rw [e1, e2]
  simp only [map_add, map_mul, map_pow]
  ring

theorem rawExtend_load32 (a : ByteArray) (i : USize) (hs : a.size < USize.size) (m : Nat)
    (h : i.toNat + 4 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a i.toNat (i.toNat + 4 + m)) =
      rawExtend (stepU32 s (load32 a i hs (by omega))) (bytes a (i.toNat + 4) (i.toNat + 4 + m)) := by
  apply eq_of_π_P
  rw [π_P_rawExtend, π_P_rawExtend, π_P_stepU32, msgPoly_bytes_load32 a i hs m h,
    length_bytes a _ _ h, length_bytes a _ _ h]
  have e1 : i.toNat + 4 + m - i.toNat = 4 + m := by omega
  have e2 : i.toNat + 4 + m - (i.toNat + 4) = m := by omega
  rw [e1, e2]
  simp only [map_add, map_mul, map_pow]
  ring

theorem rawExtend_crc128 (a : ByteArray) (p : USize) (hs : a.size < USize.size) (m : Nat)
    (h : p.toNat + 16 + m ≤ a.size) (hp : p.toNat + 16 ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a p.toNat (p.toNat + 16 + m)) =
      rawExtend (crc128 a hs p hp s) (bytes a (p.toNat + 16) (p.toNat + 16 + m)) := by
  have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  have r0 := rawExtend_load a p hs (8 + m) (by omega) s
  have r1 := rawExtend_load a (p + 8) hs m (by omega) (stepWord s (load64 a p hs (by omega)))
  simp only [hp8] at r1
  have e1 : p.toNat + 8 + (8 + m) = p.toNat + 16 + m := by omega
  have e2 : p.toNat + 8 + 8 = p.toNat + 16 := by omega
  simp only [e1, e2] at r0 r1
  unfold crc128
  dsimp only
  rw [crc32c_u64_eq, crc32c_u64_eq, loadU64LE_eq_load64, loadU64LE_eq_load64, r0, r1]

theorem rawExtend_crc512 (a : ByteArray) (p : USize) (hs : a.size < USize.size) (m : Nat)
    (h : p.toNat + 64 + m ≤ a.size) (hp : p.toNat + 64 ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a p.toNat (p.toNat + 64 + m)) =
      rawExtend (crc512 a hs p hp s) (bytes a (p.toNat + 64) (p.toNat + 64 + m)) := by
  have hp16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have hp32 : (p + 32).toNat = p.toNat + 32 := usize_add_toNat p 32 (by omega)
  have hp48 : (p + 48).toNat = p.toNat + 48 := usize_add_toNat p 48 (by omega)
  unfold crc512
  dsimp only
  rw [show p.toNat + 64 + m = p.toNat + 16 + (48 + m) by omega,
    rawExtend_crc128 a p hs (48 + m) (by omega) (by omega)]
  rw [show bytes a (p.toNat + 16) (p.toNat + 16 + (48 + m)) =
      bytes a (p + 16).toNat ((p + 16).toNat + 16 + (32 + m)) by
        congr 1 <;> omega,
    rawExtend_crc128 a (p + 16) hs (32 + m) (by omega) (by omega)]
  rw [show bytes a ((p + 16).toNat + 16) ((p + 16).toNat + 16 + (32 + m)) =
      bytes a (p + 32).toNat ((p + 32).toNat + 16 + (16 + m)) by
        congr 1 <;> omega,
    rawExtend_crc128 a (p + 32) hs (16 + m) (by omega) (by omega)]
  rw [show bytes a ((p + 32).toNat + 16) ((p + 32).toNat + 16 + (16 + m)) =
      bytes a (p + 48).toNat ((p + 48).toNat + 16 + m) by
        congr 1 <;> omega,
    rawExtend_crc128 a (p + 48) hs m (by omega) (by omega)]
  congr 2 <;> omega

/-! ### Loop-free `8/4/2/1` tail and single-stream `16 B/iter` loop -/

theorem hwTail1_eq (a : ByteArray) (i fin : USize) (hi : i.toNat ≤ fin.toNat)
    (hlt2 : fin.toNat - i.toNat < 2) (hfin : fin.toNat ≤ a.size) (s : UInt32) :
    hwTail1 a i fin hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  unfold hwTail1
  by_cases h1 : i < fin
  · have hlt : i.toNat < fin.toNat := USize.lt_iff_toNat_lt.mp h1
    have heq : fin.toNat = i.toNat + 1 := by omega
    simp only [h1, ↓reduceDIte, crc32c_u8_eq]
    rw [uget_eq a i i.toNat rfl, bytes_cons a i.toNat fin.toNat hlt hfin,
      bytes_of_le a (by omega : fin.toNat ≤ i.toNat + 1)]
    rfl
  · have hle : fin.toNat ≤ i.toNat := by
      have : ¬ i.toNat < fin.toNat := fun h => h1 (USize.lt_iff_toNat_lt.mpr h)
      omega
    simp only [h1, ↓reduceDIte, bytes_of_le a hle]
    rfl

theorem hwTail2_eq (a : ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hlt4 : fin.toNat - i.toNat < 4)
    (hfin : fin.toNat ≤ a.size) (s : UInt32) :
    hwTail2 a hs i fin hi hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
    USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
  have e2 : (2 : USize).toNat = 2 := by simp
  unfold hwTail2
  by_cases h2 : 2 ≤ fin - i
  · have h2' : 2 ≤ fin.toNat - i.toNat := by have := USize.le_iff_toNat_le.mp h2; omega
    have hi2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
    simp only [h2, ↓reduceDIte]
    rw [hwTail1_eq a (i + 2) fin (by omega) (by omega) hfin, crc32c_u16_eq, hi2]
    obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 2 + m := ⟨fin.toNat - i.toNat - 2, by omega⟩
    rw [hm, rawExtend_load16 a i hs m (by omega)]
  · have hlt2 : fin.toNat - i.toNat < 2 := by
      have : ¬ 2 ≤ (fin - i).toNat := fun h => h2 (USize.le_iff_toNat_le.mpr (by omega))
      omega
    simp only [h2, ↓reduceDIte]
    exact hwTail1_eq a i fin hi hlt2 hfin s

theorem hwTail4_eq (a : ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hlt8 : fin.toNat - i.toNat < 8)
    (hfin : fin.toNat ≤ a.size) (s : UInt32) :
    hwTail4 a hs i fin hi hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
    USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
  have e4 : (4 : USize).toNat = 4 := by simp
  unfold hwTail4
  by_cases h4 : 4 ≤ fin - i
  · have h4' : 4 ≤ fin.toNat - i.toNat := by have := USize.le_iff_toNat_le.mp h4; omega
    have hi4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
    simp only [h4, ↓reduceDIte]
    rw [hwTail2_eq a hs (i + 4) fin (by omega) (by omega) hfin, crc32c_u32_eq, hi4]
    obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 4 + m := ⟨fin.toNat - i.toNat - 4, by omega⟩
    rw [hm, rawExtend_load32 a i hs m (by omega)]
  · have hlt4 : fin.toNat - i.toNat < 4 := by
      have : ¬ 4 ≤ (fin - i).toNat := fun h => h4 (USize.le_iff_toNat_le.mpr (by omega))
      omega
    simp only [h4, ↓reduceDIte]
    exact hwTail2_eq a hs i fin hi hlt4 hfin s

theorem hwTail8_eq (a : ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hlt16 : fin.toNat - i.toNat < 16)
    (hfin : fin.toNat ≤ a.size) (s : UInt32) :
    hwTail8 a hs i fin hi hfin s = rawExtend s (bytes a i.toNat fin.toNat) := by
  have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
    USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
  have e8 : (8 : USize).toNat = 8 := by simp
  unfold hwTail8
  by_cases h8 : 8 ≤ fin - i
  · have h8' : 8 ≤ fin.toNat - i.toNat := by have := USize.le_iff_toNat_le.mp h8; omega
    have hi8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    simp only [h8, ↓reduceDIte]
    rw [hwTail4_eq a hs (i + 8) fin (by omega) (by omega) hfin, crc32c_u64_eq,
      loadU64LE_eq_load64, hi8]
    obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 8 + m := ⟨fin.toNat - i.toNat - 8, by omega⟩
    rw [hm, rawExtend_load a i hs m (by omega)]
  · have hlt8 : fin.toNat - i.toNat < 8 := by
      have : ¬ 8 ≤ (fin - i).toNat := fun h => h8 (USize.le_iff_toNat_le.mpr (by omega))
      omega
    simp only [h8, ↓reduceDIte]
    exact hwTail4_eq a hs i fin hi hlt8 hfin s

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
    have e16 : (16 : USize).toNat = 16 := by simp
    rw [hwLoop]
    by_cases h16 : 16 ≤ fin - i
    · have h16' : 16 ≤ fin.toNat - i.toNat := by
        have := USize.le_iff_toNat_le.mp h16
        rw [hsub, e16] at this; exact this
      have hi16 : (i + 16).toNat = i.toNat + 16 := usize_add_toNat i 16 (by omega)
      simp only [h16, ↓reduceDIte]
      rw [ih (fin.toNat - (i + 16).toNat) (by omega) (i + 16) (by omega) _ rfl, hi16]
      obtain ⟨m, hm⟩ : ∃ m, fin.toNat = i.toNat + 16 + m := ⟨fin.toNat - i.toNat - 16, by omega⟩
      simp only [hm]
      exact (rawExtend_crc128 a i hs m (by omega) (by omega) s).symm
    · have hlt16 : fin.toNat - i.toNat < 16 := by
        have : ¬ 16 ≤ (fin - i).toNat := fun h => h16 (USize.le_iff_toNat_le.mpr (by omega))
        omega
      simp only [h16, ↓reduceDIte]
      exact hwTail8_eq a hs i fin hi hlt16 hfin s

/-! ### Hardware multiplication (`hwMul`) and stream-shift factors (`hwShiftWords`) -/

theorem P_hwX1 : P hwX1 = X := by
  change polyR (BitVec.twoPow 32 30) = X
  simp [polyR_twoPow]

theorem P_0x01000000 : P (0x01000000 : UInt32) = X ^ 7 := by
  change polyR (BitVec.twoPow 32 24) = X ^ 7
  simp [polyR_twoPow]

theorem π_P_hwMul (a b : UInt32) :
    π (P (hwMul a b)) = π (P a) * π (P b) * π X ^ 33 := by
  rw [hwMul, crc32c_u64_eq, π_P_stepWord, P_zero]
  unfold R
  rw [polyR_clmulLo_toUInt64]
  simp only [map_zero, zero_mul, zero_add, map_mul]
  ring

/-- Shifted residue homomorphism for `hwMul`: `ψ u = π (P u) * π X ^ 33`. -/
noncomputable def ψ (u : UInt32) : Q :=
  π (P u) * π X ^ 33

theorem ψ_hwMul (a b : UInt32) : ψ (hwMul a b) = ψ a * ψ b := by
  unfold ψ
  rw [π_P_hwMul]
  ring

theorem ψ_hwOne : ψ hwOne = 1 := by
  unfold ψ hwOne
  rw [π_P_mulMod, π_P_powMod, P_0x01000000, map_pow]
  have h : π (P xInv8) ^ 5 * π X ^ 7 * π X ^ 33 = (π (P xInv8) * π X ^ 8) ^ 5 := by ring
  rw [h, π_P_xInv8, one_pow]

theorem ψ_hwX64 : ψ hwX64 = π X ^ 64 := by
  unfold ψ hwX64
  rw [π_P_powMod, P_hwX1]
  ring

theorem ψ_hwPowGo (base acc : UInt32) (n : UInt64) :
    ψ (hwPowGo base acc n) = ψ acc * (ψ base) ^ n.toNat := by
  have h : ∀ (k : Nat) (base acc : UInt32) (n : UInt64), n.toNat = k →
      ψ (hwPowGo base acc n) = ψ acc * (ψ base) ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro base acc n hk
      rw [hwPowGo]
      by_cases h0 : n = 0
      · subst h0; simp at hk; subst hk; simp
      · have hn0 : n.toNat ≠ 0 := fun hz => h0 (by rw [← n.ofNat_toNat, hz]; rfl)
        have hs : (n >>> 1).toNat = k / 2 := by rw [UInt64.toNat_shiftRight, hk]; rfl
        have hand : (n &&& 1 = 1) ↔ (k % 2 = 1) := by
          have e : (n &&& 1).toNat = k % 2 := by
            rw [← hk]
            change (n.toBitVec &&& 1#64).toNat = n.toNat % 2
            rw [BitVec.toNat_and]
            exact Nat.and_one_is_mod n.toNat
          constructor
          · intro h1; rw [← e, h1]; rfl
          · intro h1; rw [← (n &&& 1).ofNat_toNat, e, h1]; rfl
        simp only [h0, ↓reduceDIte, hand]
        rw [ih (k / 2) (by omega) _ _ (n >>> 1) hs, ψ_hwMul]
        by_cases hodd : k % 2 = 1
        · simp only [hodd, ↓reduceIte, ψ_hwMul]
          conv_rhs => rw [show k = 2 * (k / 2) + 1 by omega, pow_add, pow_mul, pow_one, sq]
          ring
        · simp only [hodd, ↓reduceIte]
          conv_rhs => rw [show k = 2 * (k / 2) by omega, pow_mul, sq]
  exact h n.toNat base acc n rfl

theorem hwShiftSmallEntry_eq (m : Fin 2048) (w r : Nat) (hw1 : 1 ≤ w) (hw : w < 512)
    (hr : r < 4) (hm : m.val = w * 4 + r) :
    hwShiftSmallEntry m = ((powMod hwX1 (64 * w - 33)) >>> (r * 8).toUInt32).toUInt8 := by
  unfold hwShiftSmallEntry
  rw [hm]
  have hd : (w * 4 + r) / 4 = w := by omega
  have hmod : (w * 4 + r) % 4 = r := by omega
  have hne : w ≠ 0 := by omega
  simp only [hd, hmod, hne, ↓reduceIte]

theorem hwShiftSmall_eq (ws : USize) (h1 : 1 ≤ ws.toNat) (hws : ws.toNat < 512) :
    hwShiftSmall ws hws = powMod hwX1 (64 * ws.toNat - 33) := by
  have hs : 2048 < USize.size := by have := usize_size_gt; omega
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
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
  unfold hwShiftSmall load32
  dsimp only
  rw [hwShiftSmallBytes_uget, hwShiftSmallBytes_uget, hwShiftSmallBytes_uget, hwShiftSmallBytes_uget,
    hwShiftSmallEntry_eq _ ws.toNat 0 h1 hws (by omega) r0,
    hwShiftSmallEntry_eq _ ws.toNat 1 h1 hws (by omega) r1,
    hwShiftSmallEntry_eq _ ws.toNat 2 h1 hws (by omega) r2,
    hwShiftSmallEntry_eq _ ws.toNat 3 h1 hws (by omega) r3]
  simpa using word32_bytes (powMod hwX1 (64 * ws.toNat - 33))

theorem ψ_hwShiftWords (ws : USize) (h1 : 1 ≤ ws.toNat) :
    ψ (hwShiftWords ws) = π X ^ (64 * ws.toNat) := by
  unfold hwShiftWords
  by_cases h : ws < 512
  · have e512 : (512 : USize).toNat = 512 := by simp
    have hlt : ws.toNat < 512 := by have := USize.lt_iff_toNat_lt.mp h; omega
    simp only [h, ↓reduceDIte, hwShiftSmall_eq ws h1 hlt]
    unfold ψ
    rw [π_P_powMod, P_hwX1, ← pow_add, show 64 * ws.toNat - 33 + 33 = 64 * ws.toNat by omega]
  · simp only [h, ↓reduceDIte, ψ_hwPowGo, ψ_hwOne, ψ_hwX64, one_mul, usize_toUInt64_toNat, ← pow_mul]

theorem π_P_hwMul_shift (u : UInt32) (ws : USize) (h1 : 1 ≤ ws.toNat) :
    π (P (hwMul u (hwShiftWords ws))) = π (P u) * π X ^ (64 * ws.toNat) := by
  rw [π_P_hwMul, mul_assoc, show π (P (hwShiftWords ws)) * π X ^ 33 = ψ (hwShiftWords ws) from rfl,
    ψ_hwShiftWords ws h1]

/-! ### Three-stream `CRC32CX` kernel (`hwFold3` and `rawExtendHw3`) -/

theorem hwFold3_spec (a : ByteArray) (hs : a.size < USize.size) (stop ws L L2 : USize)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 16 = 0)
      (s0 s1 s2 : UInt32), stop.toNat - i.toNat = k →
      hwFold3 a hs i stop ws L L2 hi hal hL2 hL s0 s1 s2 =
        combine3 ws (rawExtend s0 (bytes a i.toNat stop.toNat))
          (rawExtend s1 (bytes a (i.toNat + L.toNat) (stop.toNat + L.toNat)))
          (rawExtend s2 (bytes a (i.toNat + 2 * L.toNat) (stop.toNat + 2 * L.toNat))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal s0 s1 s2 hk
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    rw [hwFold3]
    by_cases hlt : i < stop
    · have h16le : i.toNat + 16 ≤ stop.toNat := by
        have := USize.lt_iff_toNat_lt.mp hlt; omega
      have h16 : (i + 16).toNat = i.toNat + 16 := usize_add_toNat i 16 (by omega)
      have hi1 : (i + L).toNat = i.toNat + L.toNat := by
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
        rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hlt, ↓reduceDIte]
      rw [ih (stop.toNat - (i + 16).toNat) (by omega) (i + 16) (by omega) (by omega) _ _ _ rfl]
      obtain ⟨m, hm⟩ : ∃ m, stop.toNat = i.toNat + 16 + m := ⟨stop.toNat - i.toNat - 16, by omega⟩
      have r0 := rawExtend_crc128 a i hs m (by omega) (by omega) s0
      have r1 := rawExtend_crc128 a (i + L) hs m (by omega) (by omega) s1
      have r2 := rawExtend_crc128 a (i + L2) hs m (by omega) (by omega) s2
      simp only [hi1] at r1
      simp only [hi2] at r2
      have e1 : i.toNat + 16 + L.toNat = i.toNat + L.toNat + 16 := by omega
      have e2 : i.toNat + 16 + 2 * L.toNat = i.toNat + 2 * L.toNat + 16 := by omega
      have e3 : i.toNat + 16 + m + L.toNat = i.toNat + L.toNat + 16 + m := by omega
      have e4 : i.toNat + 16 + m + 2 * L.toNat = i.toNat + 2 * L.toNat + 16 + m := by omega
      simp only [h16, hm, e1, e2, e3, e4]
      rw [← r0, ← r1, ← r2]
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      simp only [hlt, ↓reduceDIte, heq]
      rw [bytes_of_le a (Nat.le_refl _), bytes_of_le a (Nat.le_refl _), bytes_of_le a (Nat.le_refl _)]
      rfl

theorem combine3_eq (s : UInt32) (ws : USize) (h1 : 1 ≤ ws.toNat) (A B C : List UInt8)
    (hA : A.length = 8 * ws.toNat) (hB : B.length = 8 * ws.toNat) (hC : C.length = 8 * ws.toNat) :
    combine3 ws (rawExtend s A) (rawExtend 0 B) (rawExtend 0 C) = rawExtend s (A ++ B ++ C) := by
  apply eq_of_π_P
  unfold combine3
  simp only [P_xor, map_add, π_P_hwMul_shift _ ws h1, π_P_rawExtend, msgPoly_append,
    List.length_append, hA, hB, hC, P_zero, map_zero, zero_mul, zero_add, map_mul, map_pow,
    show 8 * (8 * ws.toNat) = 64 * ws.toNat by omega]
  ring

theorem rawExtendHw3_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) (h96 : 96 ≤ ulen) :
    rawExtendHw3 s a hs uoff ulen h h96 =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendHw3
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e96 : (96 : USize).toNat = 96 := by simp
  have h96' : 96 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h96; omega
  have e48 : (48 : USize).toNat = 48 := by simp
  have e16 : (16 : USize).toNat = 16 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  have hblocks : (ulen / 48).toNat = ulen.toNat / 48 := by rw [USize.toNat_div, e48]
  have hws : (ulen / 48 * 2).toNat = (ulen / 48).toNat * 2 := by
    rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL : (ulen / 48 * 16).toNat = (ulen / 48).toNat * 16 := by
    rw [USize.toNat_mul, e16]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : (2 * (ulen / 48 * 16)).toNat = 2 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : (3 * (ulen / 48 * 16)).toNat = 3 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hstop : (uoff + ulen / 48 * 16).toNat = uoff.toNat + (ulen / 48 * 16).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have htail : (uoff + 3 * (ulen / 48 * 16)).toNat = uoff.toNat + 3 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
  dsimp only
  rw [hwLoop_eq a hs _ (by omega) _ _ _ _ rfl,
    hwFold3_spec a hs _ (ulen / 48 * 2) (ulen / 48 * 16) _ hL2 (by omega) _ uoff (by omega) (by omega) _ _ _ rfl,
    htail, hfin, hstop]
  have lenA : (bytes a uoff.toNat (uoff.toNat + (ulen / 48 * 16).toNat)).length = 8 * (ulen / 48 * 2).toNat := by
    rw [length_bytes a _ _ (by omega)]; omega
  have lenB : (bytes a (uoff.toNat + (ulen / 48 * 16).toNat) (uoff.toNat + (ulen / 48 * 16).toNat + (ulen / 48 * 16).toNat)).length = 8 * (ulen / 48 * 2).toNat := by
    rw [length_bytes a _ _ (by omega)]; omega
  have lenC : (bytes a (uoff.toNat + 2 * (ulen / 48 * 16).toNat) (uoff.toNat + (ulen / 48 * 16).toNat + 2 * (ulen / 48 * 16).toNat)).length = 8 * (ulen / 48 * 2).toNat := by
    rw [length_bytes a _ _ (by omega)]; omega
  rw [combine3_eq s (ulen / 48 * 2) (by omega) _ _ _ lenA lenB lenC, ← rawExtend_append]
  have j1 : uoff.toNat + (ulen / 48 * 16).toNat + (ulen / 48 * 16).toNat = uoff.toNat + 2 * (ulen / 48 * 16).toNat := by omega
  have j2 : uoff.toNat + (ulen / 48 * 16).toNat + 2 * (ulen / 48 * 16).toNat = uoff.toNat + 3 * (ulen / 48 * 16).toNat := by omega
  rw [j1, j2,
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + (ulen / 48 * 16).toNat) (j := uoff.toNat + 2 * (ulen / 48 * 16).toNat)
      (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 2 * (ulen / 48 * 16).toNat) (j := uoff.toNat + 3 * (ulen / 48 * 16).toNat)
      (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 3 * (ulen / 48 * 16).toNat)
      (j := uoff.toNat + ulen.toNat) (by omega) (by omega) h]

/-! ### Six-stream `3 × CRC32CX + 3 × PMULL` 64-byte dot-product kernel (`hwFold6`) -/

theorem R_powMod_hwX1 (e : Nat) :
    π X * R ((powMod hwX1 e).toUInt64) = π X ^ (e + 33) := by
  unfold R
  rw [polyR_toUInt64, map_mul, map_pow, π_P_powMod, P_hwX1]
  ring

theorem R128_fold128_gen (lo hi nlo nhi k1 k2 : UInt64) (d : Nat)
    (hk1 : π X * R k1 = π X ^ (d + 64)) (hk2 : π X * R k2 = π X ^ d) :
    R128 (fold128Lo lo hi nlo k1 k2) (fold128Hi lo hi nhi k1 k2) =
      R128 lo hi * π X ^ d + R128 nlo nhi := by
  unfold fold128Lo fold128Hi
  rw [R128_xor, R128_xor, R128_clmul, R128_clmul, hk1, hk2]
  unfold R128
  simp only [pow_add]
  ring

theorem R128_fold128 (lo hi nlo nhi : UInt64) :
    R128 (fold128Lo lo hi nlo kFold128_1 kFold128_2) (fold128Hi lo hi nhi kFold128_1 kFold128_2) =
      R128 lo hi * π X ^ 128 + R128 nlo nhi :=
  R128_fold128_gen lo hi nlo nhi kFold128_1 kFold128_2 128 (R_powMod_hwX1 159) (R_powMod_hwX1 95)

theorem R128_fold256 (lo hi nlo nhi : UInt64) :
    R128 (fold128Lo lo hi nlo kFold256_1 kFold256_2) (fold128Hi lo hi nhi kFold256_1 kFold256_2) =
      R128 lo hi * π X ^ 256 + R128 nlo nhi :=
  R128_fold128_gen lo hi nlo nhi kFold256_1 kFold256_2 256 (R_powMod_hwX1 287) (R_powMod_hwX1 223)

theorem R128_fold384 (lo hi nlo nhi : UInt64) :
    R128 (fold128Lo lo hi nlo kFold384_1 kFold384_2) (fold128Hi lo hi nhi kFold384_1 kFold384_2) =
      R128 lo hi * π X ^ 384 + R128 nlo nhi :=
  R128_fold128_gen lo hi nlo nhi kFold384_1 kFold384_2 384 (R_powMod_hwX1 415) (R_powMod_hwX1 351)

theorem R128_fold512_pair (lo hi nlo nhi : UInt64) :
    R128 (fold128Lo lo hi nlo kFold512_1 kFold512_2) (fold128Hi lo hi nhi kFold512_1 kFold512_2) =
      R128 lo hi * π X ^ 512 + R128 nlo nhi :=
  R128_fold128_gen lo hi nlo nhi kFold512_1 kFold512_2 512 (R_powMod_hwX1 543) (R_powMod_hwX1 479)

theorem R128_init512 (w0 w1 w2 w3 w4 w5 u0 u1 : UInt64) :
    R128 (init512Lo w0 w1 w2 w3 w4 w5 u0) (init512Hi w0 w1 w2 w3 w4 w5 u1) =
      R128 w0 w1 * π X ^ 384 + R128 w2 w3 * π X ^ 256 +
        R128 w4 w5 * π X ^ 128 + R128 u0 u1 := by
  unfold init512Lo init512Hi
  rw [R128_fold128, R128_fold256, R128_fold384]
  ring

theorem R128_fold512 (x0 x1 w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) :
    R128 (fold512Lo x0 x1 w0 w1 w2 w3 w4 w5 w6) (fold512Hi x0 x1 w0 w1 w2 w3 w4 w5 w7) =
      R128 x0 x1 * π X ^ 512 + R128 w0 w1 * π X ^ 384 + R128 w2 w3 * π X ^ 256 +
        R128 w4 w5 * π X ^ 128 + R128 w6 w7 := by
  unfold fold512Lo fold512Hi
  rw [R128_init512, R128_fold512_pair]
  ring

theorem π_P_finish128 (lo hi : UInt64) :
    π (P (finish128 lo hi)) = R128 lo hi * π X ^ 32 := by
  unfold finish128 R128
  rw [crc32c_u64_eq, crc32c_u64_eq, π_P_stepWord, π_P_stepWord, P_zero]
  simp only [map_zero, zero_mul, zero_add]
  ring

theorem msgPoly_bytes_load128 (a : ByteArray) (p : USize) (hs : a.size < USize.size) (m : Nat)
    (h : p.toNat + 16 + m ≤ a.size) (hp8 : p.toNat + 8 ≤ a.size) (hp16 : p.toNat + 16 ≤ a.size) :
    π (msgPoly (bytes a p.toNat (p.toNat + 16 + m))) =
      R128 (SimdModels.loadU64LE a p hs hp8) (load64Hi a hs p hp16) * π X ^ (8 * m) +
        π (msgPoly (bytes a (p.toNat + 16) (p.toNat + 16 + m))) := by
  have h8 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  have m0 := msgPoly_bytes_load a p hs (8 + m) (by omega)
  have m1 := msgPoly_bytes_load a (p + 8) hs m (by omega)
  simp only [h8] at m1
  have e1 : p.toNat + 8 + (8 + m) = p.toNat + 16 + m := by omega
  have e2 : p.toNat + 8 + 8 = p.toNat + 16 := by omega
  simp only [e1, e2] at m0 m1
  unfold load64Hi R128 R
  dsimp only
  rw [loadU64LE_eq_load64, loadU64LE_eq_load64, m0, m1]
  simp only [map_add, map_mul, map_pow, Nat.mul_add, pow_add]
  ring

theorem msgPoly_bytes_load512 (a : ByteArray) (p : USize) (hs : a.size < USize.size) (m : Nat)
    (h : p.toNat + 64 + m ≤ a.size)
    (hp16 : (p + 16).toNat = p.toNat + 16)
    (hp32 : (p + 32).toNat = p.toNat + 32)
    (hp48 : (p + 48).toNat = p.toNat + 48)
    (hb0_8 : p.toNat + 8 ≤ a.size) (hb0_16 : p.toNat + 16 ≤ a.size)
    (hb1_8 : (p + 16).toNat + 8 ≤ a.size) (hb1_16 : (p + 16).toNat + 16 ≤ a.size)
    (hb2_8 : (p + 32).toNat + 8 ≤ a.size) (hb2_16 : (p + 32).toNat + 16 ≤ a.size)
    (hb3_8 : (p + 48).toNat + 8 ≤ a.size) (hb3_16 : (p + 48).toNat + 16 ≤ a.size) :
    π (msgPoly (bytes a p.toNat (p.toNat + 64 + m))) =
      (R128 (SimdModels.loadU64LE a p hs hb0_8) (load64Hi a hs p hb0_16) * π X ^ 384 +
        R128 (SimdModels.loadU64LE a (p + 16) hs hb1_8) (load64Hi a hs (p + 16) hb1_16) * π X ^ 256 +
        R128 (SimdModels.loadU64LE a (p + 32) hs hb2_8) (load64Hi a hs (p + 32) hb2_16) * π X ^ 128 +
        R128 (SimdModels.loadU64LE a (p + 48) hs hb3_8) (load64Hi a hs (p + 48) hb3_16)) * π X ^ (8 * m) +
        π (msgPoly (bytes a (p.toNat + 64) (p.toNat + 64 + m))) := by
  have m0 := msgPoly_bytes_load128 a p hs (48 + m) (by omega) hb0_8 hb0_16
  have m1 := msgPoly_bytes_load128 a (p + 16) hs (32 + m) (by omega) hb1_8 hb1_16
  have m2 := msgPoly_bytes_load128 a (p + 32) hs (16 + m) (by omega) hb2_8 hb2_16
  have m3 := msgPoly_bytes_load128 a (p + 48) hs m (by omega) hb3_8 hb3_16
  rw [show p.toNat + 64 + m = p.toNat + 16 + (48 + m) by omega, m0]
  rw [show bytes a (p.toNat + 16) (p.toNat + 16 + (48 + m)) =
      bytes a (p + 16).toNat ((p + 16).toNat + 16 + (32 + m)) by congr 1 <;> omega, m1]
  rw [show bytes a ((p + 16).toNat + 16) ((p + 16).toNat + 16 + (32 + m)) =
      bytes a (p + 32).toNat ((p + 32).toNat + 16 + (16 + m)) by congr 1 <;> omega, m2]
  rw [show bytes a ((p + 32).toNat + 16) ((p + 32).toNat + 16 + (16 + m)) =
      bytes a (p + 48).toNat ((p + 48).toNat + 16 + m) by congr 1 <;> omega, m3]
  rw [show bytes a ((p + 48).toNat + 16) ((p + 48).toNat + 16 + m) =
      bytes a (p.toNat + 64) (p.toNat + 16 + (48 + m)) by congr 1 <;> omega]
  simp only [Nat.mul_add, pow_add]
  ring

/-- Stream invariant for a 128-bit `PMULL` accumulator `(lo, hi)` at byte offset `p` up to `stop`. -/
noncomputable def pmullStreamInv (a : ByteArray) (p stop : Nat) (lo hi : UInt64) : Q :=
  (R128 lo hi * π X ^ (8 * (stop - p)) + π (msgPoly (bytes a p stop))) * π X ^ 32

theorem pmullStreamInv_step64 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (stop : Nat)
    (h64 : p.toNat + 64 ≤ stop) (hstop : stop ≤ a.size)
    (hp16 : (p + 16).toNat = p.toNat + 16)
    (hp32 : (p + 32).toNat = p.toNat + 32)
    (hp48 : (p + 48).toNat = p.toNat + 48)
    (hb0_8 : p.toNat + 8 ≤ a.size) (hb0_16 : p.toNat + 16 ≤ a.size)
    (hb1_8 : (p + 16).toNat + 8 ≤ a.size) (hb1_16 : (p + 16).toNat + 16 ≤ a.size)
    (hb2_8 : (p + 32).toNat + 8 ≤ a.size) (hb2_16 : (p + 32).toNat + 16 ≤ a.size)
    (hb3_8 : (p + 48).toNat + 8 ≤ a.size) (hb3_16 : (p + 48).toNat + 16 ≤ a.size)
    (lo hi : UInt64) :
    pmullStreamInv a (p.toNat + 64) stop
      (fold512Lo lo hi
        (SimdModels.loadU64LE a p hs hb0_8) (load64Hi a hs p hb0_16)
        (SimdModels.loadU64LE a (p + 16) hs hb1_8) (load64Hi a hs (p + 16) hb1_16)
        (SimdModels.loadU64LE a (p + 32) hs hb2_8) (load64Hi a hs (p + 32) hb2_16)
        (SimdModels.loadU64LE a (p + 48) hs hb3_8))
      (fold512Hi lo hi
        (SimdModels.loadU64LE a p hs hb0_8) (load64Hi a hs p hb0_16)
        (SimdModels.loadU64LE a (p + 16) hs hb1_8) (load64Hi a hs (p + 16) hb1_16)
        (SimdModels.loadU64LE a (p + 32) hs hb2_8) (load64Hi a hs (p + 32) hb2_16)
        (load64Hi a hs (p + 48) hb3_16)) =
    pmullStreamInv a p.toNat stop lo hi := by
  obtain ⟨m, hm⟩ : ∃ m, stop = p.toNat + 64 + m := ⟨stop - (p.toNat + 64), by omega⟩
  have hload := msgPoly_bytes_load512 a p hs m (by omega) hp16 hp32 hp48
    hb0_8 hb0_16 hb1_8 hb1_16 hb2_8 hb2_16 hb3_8 hb3_16
  unfold pmullStreamInv
  rw [R128_fold512, hm, hload]
  have e1 : p.toNat + 64 + m - (p.toNat + 64) = m := by omega
  have e2 : p.toNat + 64 + m - p.toNat = 64 + m := by omega
  rw [e1, e2]
  simp only [Nat.mul_add, pow_add]
  ring

theorem pmullStreamInv_stop (a : ByteArray) (stop : Nat) (lo hi : UInt64) :
    pmullStreamInv a stop stop lo hi = π (P (finish128 lo hi)) := by
  unfold pmullStreamInv
  rw [π_P_finish128, Nat.sub_self, Nat.mul_zero, pow_zero, bytes_of_le a (Nat.le_refl _)]
  simp [msgPoly]

theorem pmullStreamInv_init64 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (L : Nat)
    (h64 : 64 ≤ L) (hL : p.toNat + L ≤ a.size)
    (hp16 : (p + 16).toNat = p.toNat + 16)
    (hp32 : (p + 32).toNat = p.toNat + 32)
    (hp48 : (p + 48).toNat = p.toNat + 48)
    (hb0_8 : p.toNat + 8 ≤ a.size) (hb0_16 : p.toNat + 16 ≤ a.size)
    (hb1_8 : (p + 16).toNat + 8 ≤ a.size) (hb1_16 : (p + 16).toNat + 16 ≤ a.size)
    (hb2_8 : (p + 32).toNat + 8 ≤ a.size) (hb2_16 : (p + 32).toNat + 16 ≤ a.size)
    (hb3_8 : (p + 48).toNat + 8 ≤ a.size) (hb3_16 : (p + 48).toNat + 16 ≤ a.size) :
    pmullStreamInv a (p.toNat + 64) (p.toNat + L)
      (init512Lo
        (SimdModels.loadU64LE a p hs hb0_8) (load64Hi a hs p hb0_16)
        (SimdModels.loadU64LE a (p + 16) hs hb1_8) (load64Hi a hs (p + 16) hb1_16)
        (SimdModels.loadU64LE a (p + 32) hs hb2_8) (load64Hi a hs (p + 32) hb2_16)
        (SimdModels.loadU64LE a (p + 48) hs hb3_8))
      (init512Hi
        (SimdModels.loadU64LE a p hs hb0_8) (load64Hi a hs p hb0_16)
        (SimdModels.loadU64LE a (p + 16) hs hb1_8) (load64Hi a hs (p + 16) hb1_16)
        (SimdModels.loadU64LE a (p + 32) hs hb2_8) (load64Hi a hs (p + 32) hb2_16)
        (load64Hi a hs (p + 48) hb3_16)) =
      π (P (rawExtend 0 (bytes a p.toNat (p.toNat + L)))) := by
  obtain ⟨m, hm⟩ : ∃ m, L = 64 + m := ⟨L - 64, by omega⟩
  have e : p.toNat + (64 + m) = p.toNat + 64 + m := by omega
  have hload := msgPoly_bytes_load512 a p hs m (by omega) hp16 hp32 hp48
    hb0_8 hb0_16 hb1_8 hb1_16 hb2_8 hb2_16 hb3_8 hb3_16
  unfold pmullStreamInv
  rw [π_P_rawExtend, P_zero, hm, e, R128_init512, hload,
    show p.toNat + 64 + m - (p.toNat + 64) = m by omega]
  simp only [map_zero, zero_mul, zero_add]

theorem withBlock512_π_P (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt32) :
    π (P (withBlock512 a hs p hp k)) =
      withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 => π (P (k w0 w1 w2 w3 w4 w5 w6 w7))) := rfl

theorem withBlock512_add_right (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (X : Q)
    (f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Q) :
    withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 => X + f w0 w1 w2 w3 w4 w5 w6 w7) =
      X + withBlock512 a hs p hp f := rfl

theorem withBlock512_add_left (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (Y : Q)
    (f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Q) :
    withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 => f w0 w1 w2 w3 w4 w5 w6 w7 + Y) =
      withBlock512 a hs p hp f + Y := rfl

theorem withBlock512_mul_left (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (Y : Q)
    (f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Q) :
    withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 => f w0 w1 w2 w3 w4 w5 w6 w7 * Y) =
      withBlock512 a hs p hp f * Y := rfl

theorem withBlock512_pmullStep (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (stop : Nat)
    (h64 : p.toNat + 64 ≤ stop) (hstop : stop ≤ a.size) (lo hi : UInt64) :
    withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 =>
      pmullStreamInv a (p.toNat + 64) stop
        (fold512Lo lo hi w0 w1 w2 w3 w4 w5 w6)
        (fold512Hi lo hi w0 w1 w2 w3 w4 w5 w7)) =
    pmullStreamInv a p.toNat stop lo hi := by
  have hp16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have hp32 : (p + 32).toNat = p.toNat + 32 := usize_add_toNat p 32 (by omega)
  have hp48 : (p + 48).toNat = p.toNat + 48 := usize_add_toNat p 48 (by omega)
  unfold withBlock512
  dsimp only
  exact pmullStreamInv_step64 a hs p stop h64 hstop hp16 hp32 hp48
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) lo hi

theorem withBlock512_pmullInit (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (L : Nat)
    (h64 : 64 ≤ L) (hL : p.toNat + L ≤ a.size) :
    withBlock512 a hs p hp (fun w0 w1 w2 w3 w4 w5 w6 w7 =>
      pmullStreamInv a (p.toNat + 64) (p.toNat + L)
        (init512Lo w0 w1 w2 w3 w4 w5 w6)
        (init512Hi w0 w1 w2 w3 w4 w5 w7)) =
    π (P (rawExtend 0 (bytes a p.toNat (p.toNat + L)))) := by
  have hp16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have hp32 : (p + 32).toNat = p.toNat + 32 := usize_add_toNat p 32 (by omega)
  have hp48 : (p + 48).toNat = p.toNat + 48 := usize_add_toNat p 48 (by omega)
  unfold withBlock512
  dsimp only
  exact pmullStreamInv_init64 a hs p L h64 hL hp16 hp32 hp48
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem π_P_combine6 (ws : USize) (h1 : 1 ≤ ws.toNat) (s0 s1 s2 s3 s4 s5 : UInt32) :
    π (P (combine6 ws s0 s1 s2 s3 s4 s5)) =
      (((((π (P s0) * π X ^ (64 * ws.toNat) + π (P s1)) * π X ^ (64 * ws.toNat) + π (P s2)) *
        π X ^ (64 * ws.toNat) + π (P s3)) * π X ^ (64 * ws.toNat) + π (P s4)) *
        π X ^ (64 * ws.toNat) + π (P s5)) := by
  unfold combine6
  have hf2 : ∀ u : UInt32,
      π (P (hwMul u (hwMul (hwShiftWords ws) (hwShiftWords ws)))) =
        π (P u) * (π X ^ (64 * ws.toNat)) ^ 2 := by
    intro u
    rw [π_P_hwMul, mul_assoc,
      show π (P (hwMul (hwShiftWords ws) (hwShiftWords ws))) * π X ^ 33 =
        ψ (hwMul (hwShiftWords ws) (hwShiftWords ws)) from rfl,
      ψ_hwMul, ψ_hwShiftWords ws h1, sq]
  simp only [P_xor, map_add, hf2, π_P_hwMul_shift _ ws h1]
  ring

theorem hwFold6Loop_spec (a : ByteArray) (hs : a.size < USize.size)
    (stop ws L L2 L3 L4 L5 : USize)
    (h1 : 1 ≤ ws.toNat)
    (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat) (hL5 : L5.toNat = 5 * L.toNat)
    (hL : stop.toNat + 5 * L.toNat ≤ a.size) :
    ∀ (k : Nat) (i : USize) (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 64 = 0)
      (s0 s1 s2 : UInt32) (a0 a1 b0 b1 c0 c1 : UInt64),
      stop.toNat - i.toNat = k →
      π (P (hwFold6Loop a hs i stop ws L L2 L3 L4 L5 hi hal hL2 hL3 hL4 hL5 hL
          s0 s1 s2 a0 a1 b0 b1 c0 c1)) =
        (((((π (P (rawExtend s0 (bytes a i.toNat stop.toNat))) * π X ^ (64 * ws.toNat) +
              π (P (rawExtend s1 (bytes a (i.toNat + L.toNat) (stop.toNat + L.toNat))))) *
                π X ^ (64 * ws.toNat) +
              π (P (rawExtend s2 (bytes a (i.toNat + 2 * L.toNat) (stop.toNat + 2 * L.toNat))))) *
                π X ^ (64 * ws.toNat) +
              pmullStreamInv a (i.toNat + 3 * L.toNat) (stop.toNat + 3 * L.toNat) a0 a1) *
                π X ^ (64 * ws.toNat) +
              pmullStreamInv a (i.toNat + 4 * L.toNat) (stop.toNat + 4 * L.toNat) b0 b1) *
                π X ^ (64 * ws.toNat) +
              pmullStreamInv a (i.toNat + 5 * L.toNat) (stop.toNat + 5 * L.toNat) c0 c1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi hal s0 s1 s2 a0 a1 b0 b1 c0 c1 hk
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    rw [hwFold6Loop]
    by_cases hlt : i < stop
    · have h64le : i.toNat + 64 ≤ stop.toNat := by
        have := USize.lt_iff_toNat_lt.mp hlt; omega
      have h64 : (i + 64).toNat = i.toNat + 64 := usize_add_toNat i 64 (by omega)
      have hi1 : (i + L).toNat = i.toNat + L.toNat := by
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
        rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
      have hi3 : (i + L3).toNat = i.toNat + 3 * L.toNat := by
        rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
      have hi4 : (i + L4).toNat = i.toNat + 4 * L.toNat := by
        rw [USize.toNat_add, hL4]; exact Nat.mod_eq_of_lt (by omega)
      have hi5 : (i + L5).toNat = i.toNat + 5 * L.toNat := by
        rw [USize.toNat_add, hL5]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hlt, ↓reduceDIte]
      simp only [withBlock512_π_P]
      have sh3 : (i + 64).toNat + 3 * L.toNat = (i + L3).toNat + 64 := by omega
      have sh4 : (i + 64).toNat + 4 * L.toNat = (i + L4).toNat + 64 := by omega
      have sh5 : (i + 64).toNat + 5 * L.toNat = (i + L5).toNat + 64 := by omega
      simp_rw [ih (stop.toNat - (i + 64).toNat) (by omega) (i + 64) (by omega) (by omega)
        _ _ _ _ _ _ _ _ _ rfl, sh3, sh4, sh5]
      simp only [withBlock512_add_right, withBlock512_add_left, withBlock512_mul_left]
      rw [withBlock512_pmullStep a hs (i + L3) _ (stop.toNat + 3 * L.toNat) (by omega) (by omega) a0 a1,
        withBlock512_pmullStep a hs (i + L4) _ (stop.toNat + 4 * L.toNat) (by omega) (by omega) b0 b1,
        withBlock512_pmullStep a hs (i + L5) _ (stop.toNat + 5 * L.toNat) (by omega) (by omega) c0 c1,
        hi3, hi4, hi5]
      obtain ⟨m, hm⟩ : ∃ m, stop.toNat = i.toNat + 64 + m := ⟨stop.toNat - i.toNat - 64, by omega⟩
      have r0 := rawExtend_crc512 a i hs m (by omega) (by omega) s0
      have r1 := rawExtend_crc512 a (i + L) hs m (by omega) (by omega) s1
      have r2 := rawExtend_crc512 a (i + L2) hs m (by omega) (by omega) s2
      simp only [hi1] at r1
      simp only [hi2] at r2
      have e3 : i.toNat + 64 + m + L.toNat = i.toNat + L.toNat + 64 + m := by omega
      have e4 : i.toNat + 64 + m + 2 * L.toNat = i.toNat + 2 * L.toNat + 64 + m := by omega
      simp only [h64, hm]
      simp only [e3, e4]
      rw [show i.toNat + 64 + L.toNat = i.toNat + L.toNat + 64 by omega,
        show i.toNat + 64 + 2 * L.toNat = i.toNat + 2 * L.toNat + 64 by omega,
        ← r0, ← r1, ← r2]
    · have heq : i.toNat = stop.toNat := by
        have : ¬ i.toNat < stop.toNat := fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
        omega
      simp only [hlt, ↓reduceDIte, π_P_combine6 ws h1, heq,
        pmullStreamInv_stop, bytes_of_le a (Nat.le_refl _)]
      rfl

theorem hwFold6_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff blocks : USize) (hb : 1 ≤ blocks.toNat)
    (h : uoff.toNat + blocks.toNat * 384 ≤ a.size) :
    hwFold6 s a hs uoff blocks hb h =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + blocks.toNat * 384)) := by
  apply eq_of_π_P
  unfold hwFold6
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e64 : (64 : USize).toNat = 64 := by simp
  have e8 : (8 : USize).toNat = 8 := by simp
  have e5 : (5 : USize).toNat = 5 := by simp
  have e4 : (4 : USize).toNat = 4 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  have hws : (blocks * 8).toNat = blocks.toNat * 8 := by
    rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
  have hL : (blocks * 64).toNat = blocks.toNat * 64 := by
    rw [USize.toNat_mul, e64]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : (2 * (blocks * 64)).toNat = 2 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : (3 * (blocks * 64)).toNat = 3 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hL4 : (4 * (blocks * 64)).toNat = 4 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e4]; exact Nat.mod_eq_of_lt (by omega)
  have hL5 : (5 * (blocks * 64)).toNat = 5 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e5]; exact Nat.mod_eq_of_lt (by omega)
  have hu64 : (uoff + 64).toNat = uoff.toNat + 64 := usize_add_toNat uoff 64 (by omega)
  have hp1 : (uoff + blocks * 64).toNat = uoff.toNat + (blocks * 64).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp2 : (uoff + 2 * (blocks * 64)).toNat = uoff.toNat + 2 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (uoff + 3 * (blocks * 64)).toNat = uoff.toNat + 3 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
  have hp4 : (uoff + 4 * (blocks * 64)).toNat = uoff.toNat + 4 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL4]; exact Nat.mod_eq_of_lt (by omega)
  have hp5 : (uoff + 5 * (blocks * 64)).toNat = uoff.toNat + 5 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL5]; exact Nat.mod_eq_of_lt (by omega)
  dsimp only
  simp only [withBlock512_π_P]
  let Ln := (blocks * 64).toNat
  have hLn64 : 64 ≤ Ln := by show 64 ≤ (blocks * 64).toNat; omega
  obtain ⟨m, hm⟩ : ∃ m, Ln = 64 + m := ⟨Ln - 64, by omega⟩
  have r0 := rawExtend_crc512 a uoff hs m (by omega) (by omega) s
  have r1 := rawExtend_crc512 a (uoff + blocks * 64) hs m (by omega) (by omega) 0
  have r2 := rawExtend_crc512 a (uoff + 2 * (blocks * 64)) hs m (by omega) (by omega) 0
  have sh1 : (uoff + 64).toNat + Ln = (uoff + blocks * 64).toNat + 64 := by show _ + (blocks * 64).toNat = _; omega
  have sh2 : (uoff + 64).toNat + 2 * Ln = (uoff + 2 * (blocks * 64)).toNat + 64 := by show _ + 2 * (blocks * 64).toNat = _; omega
  have sh3 : (uoff + 64).toNat + 3 * Ln = (uoff + 3 * (blocks * 64)).toNat + 64 := by show _ + 3 * (blocks * 64).toNat = _; omega
  have sh4 : (uoff + 64).toNat + 4 * Ln = (uoff + 4 * (blocks * 64)).toNat + 64 := by show _ + 4 * (blocks * 64).toNat = _; omega
  have sh5 : (uoff + 64).toNat + 5 * Ln = (uoff + 5 * (blocks * 64)).toNat + 64 := by show _ + 5 * (blocks * 64).toNat = _; omega
  have end0 : (uoff + blocks * 64).toNat = uoff.toNat + 64 + m := by omega
  have end1 : (uoff + blocks * 64).toNat + Ln = (uoff + blocks * 64).toNat + 64 + m := by show _ + (blocks * 64).toNat = _; omega
  have end2 : (uoff + blocks * 64).toNat + 2 * Ln = (uoff + 2 * (blocks * 64)).toNat + 64 + m := by show _ + 2 * (blocks * 64).toNat = _; omega
  have end3 : (uoff + blocks * 64).toNat + 3 * Ln = (uoff + 3 * (blocks * 64)).toNat + Ln := by show _ + 3 * (blocks * 64).toNat = _ + (blocks * 64).toNat; omega
  have end4 : (uoff + blocks * 64).toNat + 4 * Ln = (uoff + 4 * (blocks * 64)).toNat + Ln := by show _ + 4 * (blocks * 64).toNat = _ + (blocks * 64).toNat; omega
  have end5 : (uoff + blocks * 64).toNat + 5 * Ln = (uoff + 5 * (blocks * 64)).toNat + Ln := by show _ + 5 * (blocks * 64).toNat = _ + (blocks * 64).toNat; omega
  simp_rw [hwFold6Loop_spec a hs (uoff + blocks * 64) (blocks * 8) (blocks * 64)
    _ _ _ _ (by omega) hL2 hL3 hL4 hL5 (by omega) _ (uoff + 64) (by omega) (by omega)
    _ _ _ _ _ _ _ _ _ rfl]
  simp only [withBlock512_add_right, withBlock512_add_left, withBlock512_mul_left]
  change (((((π (P (rawExtend _ (bytes a (uoff + 64).toNat (uoff + blocks * 64).toNat))) * _ +
      π (P (rawExtend _ (bytes a ((uoff + 64).toNat + Ln) ((uoff + blocks * 64).toNat + Ln))))) * _ +
      π (P (rawExtend _ (bytes a ((uoff + 64).toNat + 2 * Ln) ((uoff + blocks * 64).toNat + 2 * Ln))))) * _ +
      withBlock512 a hs (uoff + 3 * (blocks * 64)) _
        (fun w0 w1 w2 w3 w4 w5 w6 w7 =>
          pmullStreamInv a ((uoff + 64).toNat + 3 * Ln) ((uoff + blocks * 64).toNat + 3 * Ln)
            (init512Lo w0 w1 w2 w3 w4 w5 w6) (init512Hi w0 w1 w2 w3 w4 w5 w7))) * _ +
      withBlock512 a hs (uoff + 4 * (blocks * 64)) _
        (fun w0 w1 w2 w3 w4 w5 w6 w7 =>
          pmullStreamInv a ((uoff + 64).toNat + 4 * Ln) ((uoff + blocks * 64).toNat + 4 * Ln)
            (init512Lo w0 w1 w2 w3 w4 w5 w6) (init512Hi w0 w1 w2 w3 w4 w5 w7))) * _ +
      withBlock512 a hs (uoff + 5 * (blocks * 64)) _
        (fun w0 w1 w2 w3 w4 w5 w6 w7 =>
          pmullStreamInv a ((uoff + 64).toNat + 5 * Ln) ((uoff + blocks * 64).toNat + 5 * Ln)
            (init512Lo w0 w1 w2 w3 w4 w5 w6) (init512Hi w0 w1 w2 w3 w4 w5 w7))) = _
  simp_rw [sh1, sh2, sh3, sh4, sh5, end1, end2, end3, end4, end5]
  rw [withBlock512_pmullInit a hs (uoff + 3 * (blocks * 64)) _ Ln hLn64 (by show _ + (blocks * 64).toNat ≤ _; omega),
    withBlock512_pmullInit a hs (uoff + 4 * (blocks * 64)) _ Ln hLn64 (by show _ + (blocks * 64).toNat ≤ _; omega),
    withBlock512_pmullInit a hs (uoff + 5 * (blocks * 64)) _ Ln hLn64 (by show _ + (blocks * 64).toNat ≤ _; omega)]
  rw [show bytes a (uoff + 64).toNat (uoff + blocks * 64).toNat =
    bytes a (uoff.toNat + 64) (uoff.toNat + 64 + m) by rw [hu64, end0],
    ← r0, ← r1, ← r2]
  have e512 : 64 * (blocks * 8).toNat = 8 * Ln := by show 64 * (blocks * 8).toNat = 8 * (blocks * 64).toNat; omega
  have step (u : UInt32) (x y : Nat) (hlen : (bytes a x y).length = Ln) :
      π (P u) * π X ^ (64 * (blocks * 8).toNat) + π (P (rawExtend 0 (bytes a x y))) =
        π (P (rawExtend u (bytes a x y))) := by
    rw [e512, π_P_rawExtend, π_P_rawExtend, P_zero, hlen]
    simp
  have q0 : uoff.toNat + 64 + m = uoff.toNat + Ln := by omega
  have q1 : (uoff + blocks * 64).toNat + 64 + m = uoff.toNat + 2 * Ln := by show _ = _ + 2 * (blocks * 64).toNat; omega
  have q2 : (uoff + 2 * (blocks * 64)).toNat + 64 + m = uoff.toNat + 3 * Ln := by show _ = _ + 3 * (blocks * 64).toNat; omega
  have q3 : (uoff + 3 * (blocks * 64)).toNat + Ln = uoff.toNat + 4 * Ln := by show _ + (blocks * 64).toNat = _ + 4 * (blocks * 64).toNat; omega
  have q4 : (uoff + 4 * (blocks * 64)).toNat + Ln = uoff.toNat + 5 * Ln := by show _ + (blocks * 64).toNat = _ + 5 * (blocks * 64).toNat; omega
  have q5 : (uoff + 5 * (blocks * 64)).toNat + Ln = uoff.toNat + 6 * Ln := by show _ + (blocks * 64).toNat = _ + 6 * (blocks * 64).toNat; omega
  rw [q0, q1, q2, q3, q4, q5, hp1, hp2, hp3, hp4, hp5]
  change (((((π (P (rawExtend s (bytes a uoff.toNat (uoff.toNat + Ln)))) * _ +
      π (P (rawExtend 0 (bytes a (uoff.toNat + Ln) (uoff.toNat + 2 * Ln))))) * _ +
      π (P (rawExtend 0 (bytes a (uoff.toNat + 2 * Ln) (uoff.toNat + 3 * Ln))))) * _ +
      π (P (rawExtend 0 (bytes a (uoff.toNat + 3 * Ln) (uoff.toNat + 4 * Ln))))) * _ +
      π (P (rawExtend 0 (bytes a (uoff.toNat + 4 * Ln) (uoff.toNat + 5 * Ln))))) * _ +
      π (P (rawExtend 0 (bytes a (uoff.toNat + 5 * Ln) (uoff.toNat + 6 * Ln))))) = _
  have h6L : uoff.toNat + 6 * Ln ≤ a.size := by show uoff.toNat + 6 * (blocks * 64).toNat ≤ a.size; omega
  rw [step _ (uoff.toNat + Ln) (uoff.toNat + 2 * Ln) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (uoff.toNat + 2 * Ln) (uoff.toNat + 3 * Ln) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (uoff.toNat + 3 * Ln) (uoff.toNat + 4 * Ln) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (uoff.toNat + 4 * Ln) (uoff.toNat + 5 * Ln) (by rw [length_bytes a _ _ (by omega)]; omega),
    step _ (uoff.toNat + 5 * Ln) (uoff.toNat + 6 * Ln) (by rw [length_bytes a _ _ (by omega)]; omega)]
  simp only [← rawExtend_append,
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + Ln) (j := uoff.toNat + 2 * Ln) (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 2 * Ln) (j := uoff.toNat + 3 * Ln) (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 3 * Ln) (j := uoff.toNat + 4 * Ln) (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 4 * Ln) (j := uoff.toNat + 5 * Ln) (by omega) (by omega) (by omega),
    bytes_append a (i := uoff.toNat) (m := uoff.toNat + 5 * Ln) (j := uoff.toNat + 6 * Ln) (by omega) (by omega) h6L]
  rw [show uoff.toNat + 6 * Ln = uoff.toNat + blocks.toNat * 384 by show _ + 6 * (blocks * 64).toNat = _; omega]

/-! ### Top-level dispatch (`fast_eq_ref` and spec) -/

theorem rawExtendHwMulti_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) (h96 : 96 ≤ ulen) :
    rawExtendHwMulti s a hs uoff ulen h h96 =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendHwMulti
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h768 : 768 ≤ ulen
  · have e768 : (768 : USize).toNat = 768 := by simp
    have h768' : 768 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h768; omega
    have e384 : (384 : USize).toNat = 384 := by simp
    have hblocks : (ulen / 384).toNat = ulen.toNat / 384 := by rw [USize.toNat_div, e384]
    have hcons : (ulen / 384 * 384).toNat = (ulen / 384).toNat * 384 := by
      rw [USize.toNat_mul, e384]; exact Nat.mod_eq_of_lt (by omega)
    have htail : (uoff + ulen / 384 * 384).toNat = uoff.toNat + (ulen / 384).toNat * 384 := by
      rw [USize.toNat_add, hcons]; exact Nat.mod_eq_of_lt (by omega)
    have hrem : (ulen - ulen / 384 * 384).toNat = ulen.toNat - (ulen / 384).toNat * 384 := by
      rw [USize.toNat_sub_of_le ulen (ulen / 384 * 384)
        (USize.le_iff_toNat_le.mpr (by omega)), hcons]
    simp only [h768, ↓reduceDIte]
    by_cases hrem96 : 96 ≤ ulen - ulen / 384 * 384
    · simp only [hrem96, ↓reduceDIte, rawExtendHw3_eq, hwFold6_eq, htail, hrem,
        show uoff.toNat + (ulen / 384).toNat * 384 + (ulen.toNat - (ulen / 384).toNat * 384) =
          uoff.toNat + ulen.toNat by omega]
      rw [← rawExtend_append, bytes_append a (by omega) (by omega) h]
    · simp only [hrem96, ↓reduceDIte]
      rw [hwLoop_eq a hs _ (by omega) _ _ _ _ rfl, hwFold6_eq, htail, hfin,
        ← rawExtend_append, bytes_append a (by omega) (by omega) h]
  · simp only [h768, ↓reduceDIte, rawExtendHw3_eq]

theorem rawExtendHwUSize_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) :
    rawExtendHwUSize s a hs uoff ulen h =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendHwUSize
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h96 : 96 ≤ ulen
  · simp only [h96, ↓reduceDIte, rawExtendHwMulti_eq]
  · simp only [h96, ↓reduceDIte]
    rw [hwLoop_eq a hs _ (by omega) _ _ _ _ rfl, hfin]

/-- The hardware path computes the reference update on any in-bounds range. -/
theorem rawExtendHw_eq (s : UInt32) (a : ByteArray) (off len : Nat) (h : off + len ≤ a.size) :
    rawExtendHw s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendHw
  by_cases hsmall : a.size ≤ 0x7FFFFFFF
  · have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    simp only [hsmall, ↓reduceDIte, rawExtendHwUSize_eq, ho, hl]
  · simp only [hsmall, ↓reduceDIte, rawExtendPortableCold_eq]

/-- `fast_eq_ref`, hardware path: equal to the bitwise reference on every input. -/
theorem extendHw_eq_extend (c : UInt32) (a : ByteArray) : extendHw c a = extend c a := by
  simp [extendHw, extend, rawExtendHw_eq, bytes_whole]

/-- The hardware path satisfies the polynomial spec. -/
theorem extendHw_eq_spec (c : UInt32) (a : ByteArray) : extendHw c a = Spec.extend c a := by
  rw [extendHw_eq_extend, extend_eq_spec]

end Crc32c
