/-
Machine-code verification of `_lp_leanmemcpy_Crc32c_hwLoop___redArg` (`99` instructions)
from `Hw.c.o` against `Crc32c.rawExtend s (Crc32c.bytes data i.toNat fin.toNat)`.

Covers the 16-byte-per-iteration `ldp` + `2 × crc32cx` inner loop (`idx = 5..12`) and
all 16 paths (`r = 0..15`) of the loop-free `8/4/2/1`-byte hardware tail (`idx = 13..98`),
proving termination, functional correctness, zero stack usage (`s'.mem = s.mem`,
`s'.sp = s.sp`), guard-page safety (requiring `.ro` permission only on payload bytes
`[objPtr + 0x18, objPtr + 0x18 + data.size)`, never reading `[objPtr, objPtr + 0x18)`),
and full AAPCS64 callee-saved register preservation (`CalleeSaved s s'`).
Kernel-checked without `bv_decide`.
-/
import MemcpyCrc32c.Arm64.Step

namespace Crc32c.Arm64MC
open SimdModels

/-! ### `UInt64` pointer & offset arithmetic helpers (reused across `HwLoop`, `HwFold6`, `Multi`, `ExtendHwRaw`) -/

instance : Std.Associative (· + · : UInt64 → UInt64 → UInt64) := ⟨UInt64.add_assoc⟩
instance : Std.Commutative (· + · : UInt64 → UInt64 → UInt64) := ⟨UInt64.add_comm⟩

theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem nat_toUInt64_toNat (a : Nat) (ha : a < 2 ^ 64) : a.toUInt64.toNat = a := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt ha

theorem nat_add_toUInt64 (a b : Nat) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by
  apply UInt64.eq_of_toBitVec_eq
  simp [Nat.toUInt64, UInt64.ofNat, BitVec.ofNat_add]

theorem nat_sub_toUInt64 (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  apply u64_ext
  have hb : b < 2 ^ 64 := by omega
  have hab : a - b < 2 ^ 64 := by omega
  have ha' := nat_toUInt64_toNat a ha
  have hb' := nat_toUInt64_toNat b hb
  have hle : b.toUInt64 ≤ a.toUInt64 := by
    change b.toUInt64.toNat ≤ a.toUInt64.toNat; omega
  rw [UInt64.toNat_sub_of_le a.toUInt64 b.toUInt64 hle, ha', hb', nat_toUInt64_toNat (a - b) hab]

theorem add_neg8_cancel (x : UInt64) : (x + 8) + 0xfffffffffffffff8 = x := by
  rw [UInt64.add_assoc]
  exact UInt64.add_zero x

theorem usize_le_2pow64 : USize.size ≤ 2 ^ 64 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.size, h]

theorem nat_toUSize_add_le {n k sz : Nat} (hs : sz < USize.size) (h : n + k ≤ sz) :
    n.toUSize.toNat + k ≤ sz := by
  have hn : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' (by omega)
  omega

theorem u64_lt_iff_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a.toUInt64 < b.toUInt64) ↔ a < b := by
  change a.toUInt64.toNat < b.toUInt64.toNat ↔ a < b
  rw [nat_toUInt64_toNat a ha, nat_toUInt64_toNat b hb]

theorem u64_le_iff_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a.toUInt64 ≤ b.toUInt64) ↔ a ≤ b := by
  change a.toUInt64.toNat ≤ b.toUInt64.toNat ↔ a ≤ b
  rw [nat_toUInt64_toNat a ha, nat_toUInt64_toNat b hb]

theorem lit_lt_toUInt64_1 {b : Nat} (hb : b < 2 ^ 64) : ((1 : UInt64) < b.toUInt64) ↔ 1 < b :=
  u64_lt_iff_nat (a := 1) (by omega) hb

theorem lit_lt_toUInt64_3 {b : Nat} (hb : b < 2 ^ 64) : ((3 : UInt64) < b.toUInt64) ↔ 3 < b :=
  u64_lt_iff_nat (a := 3) (by omega) hb

theorem lit_lt_toUInt64_7 {b : Nat} (hb : b < 2 ^ 64) : ((7 : UInt64) < b.toUInt64) ↔ 7 < b :=
  u64_lt_iff_nat (a := 7) (by omega) hb

theorem toUInt64_lt_16 {a : Nat} (ha : a < 2 ^ 64) : (a.toUInt64 < (16 : UInt64)) ↔ a < 16 :=
  u64_lt_iff_nat (b := 16) ha (by omega)

theorem lit_le_toUInt64_16 {b : Nat} (hb : b < 2 ^ 64) : ((16 : UInt64) ≤ b.toUInt64) ↔ 16 ≤ b :=
  u64_le_iff_nat (a := 16) (by omega) hb

@[simp] theorem nat_toUInt32_8 : (8 : Nat).toUInt32 = 8 := rfl
@[simp] theorem nat_toUInt32_16 : (16 : Nat).toUInt32 = 16 := rfl
@[simp] theorem nat_toUInt32_24 : (24 : Nat).toUInt32 = 24 := rfl

/-! ### `fin`-indexed `rawExtend` absorption and `.ro` payload read helpers -/

theorem rawExtend_u8_fin (a : ByteArray) (off fin : Nat)
    (hoff : off + 1 ≤ fin) (hfin : fin ≤ a.size) (s : UInt32) :
    Crc32c.rawExtend s (Crc32c.bytes a off fin) =
      Crc32c.rawExtend (SimdModels.crc32c_u8 s (a[off]'(by omega)))
        (Crc32c.bytes a (off + 1) fin) := by
  have h := rawExtend_u8_at a off (fin - (off + 1)) (by omega) s
  have heq : off + 1 + (fin - (off + 1)) = fin := by omega
  simpa only [heq] using h

theorem rawExtend_u16_fin (a : ByteArray) (hs : a.size < USize.size)
    (off fin : Nat) (hoff : off + 2 ≤ fin) (hfin : fin ≤ a.size) (s : UInt32) :
    Crc32c.rawExtend s (Crc32c.bytes a off fin) =
      Crc32c.rawExtend
        (SimdModels.crc32c_u16 s (Crc32c.word16 (a[off]'(by omega)) (a[off + 1]'(by omega))))
        (Crc32c.bytes a (off + 2) fin) := by
  have h := rawExtend_u16_at a hs off (fin - (off + 2)) (by omega) s
  have heq : off + 2 + (fin - (off + 2)) = fin := by omega
  simpa only [heq] using h

theorem rawExtend_u32_fin (a : ByteArray) (hs : a.size < USize.size)
    (off fin : Nat) (hoff : off + 4 ≤ fin) (hfin : fin ≤ a.size) (s : UInt32) :
    Crc32c.rawExtend s (Crc32c.bytes a off fin) =
      Crc32c.rawExtend
        (SimdModels.crc32c_u32 s
          (Crc32c.word32 (a[off]'(by omega)) (a[off + 1]'(by omega))
            (a[off + 2]'(by omega)) (a[off + 3]'(by omega))))
        (Crc32c.bytes a (off + 4) fin) := by
  have h := rawExtend_u32_at a hs off (fin - (off + 4)) (by omega) s
  have heq : off + 4 + (fin - (off + 4)) = fin := by omega
  simpa only [heq] using h

theorem rawExtend_u64_fin (a : ByteArray) (hs : a.size < USize.size)
    (off fin : Nat) (hoff : off + 8 ≤ fin) (hfin : fin ≤ a.size) (s : UInt32) :
    Crc32c.rawExtend s (Crc32c.bytes a off fin) =
      Crc32c.rawExtend
        (SimdModels.crc32c_u64 s
          (SimdModels.loadU64LE a off.toUSize hs (nat_toUSize_add_le hs (by omega))))
        (Crc32c.bytes a (off + 8) fin) := by
  have h := rawExtend_u64_at a hs off (fin - (off + 8)) (by omega) s
  have heq : off + 8 + (fin - (off + 8)) = fin := by omega
  simpa only [heq] using h

theorem ro_readU8 {m : Arm64.Mem} {objPtr : UInt64} (addr : UInt64) {data : ByteArray}
    (hro : m.hasROBytes (objPtr + 0x18) data) (k : Nat) (hk : k < data.size)
    (ha : addr = (objPtr + 0x18) + k.toUInt64) :
    m.readU8 addr = some data[k] := by
  rw [ha]; exact Arm64.Mem.hasROBytes_readU8 hro k hk

theorem ro_readU16 {m : Arm64.Mem} {objPtr : UInt64} (addr : UInt64) {data : ByteArray}
    (hro : m.hasROBytes (objPtr + 0x18) data) (k : Nat) (hk : k + 2 ≤ data.size)
    (ha : addr = (objPtr + 0x18) + k.toUInt64) :
    m.readU16LE addr = some (Crc32c.word16 (data[k]'(by omega)) (data[k + 1]'(by omega))) := by
  rw [ha]; exact Arm64.Mem.hasROBytes_readU16LE hro k hk

theorem ro_readU32 {m : Arm64.Mem} {objPtr : UInt64} (addr : UInt64) {data : ByteArray}
    (hro : m.hasROBytes (objPtr + 0x18) data) (k : Nat) (hk : k + 4 ≤ data.size)
    (ha : addr = (objPtr + 0x18) + k.toUInt64) :
    m.readU32LE addr =
      some (Crc32c.word32 (data[k]'(by omega)) (data[k + 1]'(by omega))
        (data[k + 2]'(by omega)) (data[k + 3]'(by omega))) := by
  rw [ha]; exact Arm64.Mem.hasROBytes_readU32LE hro k hk

theorem ro_readU64 {m : Arm64.Mem} {objPtr : UInt64} (addr : UInt64) {data : ByteArray}
    (hro : m.hasROBytes (objPtr + 0x18) data) (hs : data.size < USize.size)
    (k : Nat) (hk : k + 8 ≤ data.size)
    (ha : addr = (objPtr + 0x18) + k.toUInt64) :
    m.readU64LE addr =
      some (SimdModels.loadU64LE data k.toUSize hs (nat_toUSize_add_le hs hk)) := by
  rw [ha]; exact hasROBytes_readU64LE_nat hro hs k hk

/-! ### Shared exit join points of `hwLoop` (`idx = 97..98`, `idx = 94..96`, `idx = 81..85`) -/

/-- Even-remainder exit (`idx = 97..98`, `L.hwLoopBase + 388`): `mov x0, x3; ret`. -/
private theorem hwLoop_exit_even {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s0 s : Arm64.ArmState} {data : ByteArray} {off fin : Nat} {acc : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hpc : s.pc = L.hwLoopBase + 388)
    (hacc : s.getW r3 = acc)
    (heq : off = fin)
    (hmem : s.mem = s0.mem)
    (hcs : CalleeSaved s0 s) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s0.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes data off fin) ∧
      s'.mem = s0.mem ∧ CalleeSaved s0 s' := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hpc hacc hmem
  subst hpc
  mc_step_ex step_hwLoop hc 97 hwLoopInsn
  mc_step_ex step_hwLoop hc 98 hwLoopInsn
  refine ⟨0, _, Arm64.run_zero _ _, hcs.x30, ?_, hmem,
    ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
     hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
     hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩⟩
  rw [Crc32c.bytes_of_le data (by omega)]
  exact hacc

/-- Odd-remainder exit (`idx = 94..96`, `L.hwLoopBase + 376`): `ldrb w8, [x8]; crc32cb w0, w3, w8; ret`. -/
private theorem hwLoop_exit_odd {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s0 s : Arm64.ArmState} {objPtr : UInt64} {data : ByteArray} {off fin : Nat} {acc : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) data)
    (hpc : s.pc = L.hwLoopBase + 376)
    (hx8 : s.regs.x8 = (objPtr + 0x18) + off.toUInt64)
    (hacc : s.getW r3 = acc)
    (hoff : off + 1 = fin)
    (hfin : fin ≤ data.size)
    (hmem : s.mem = s0.mem)
    (hcs : CalleeSaved s0 s) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s0.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes data off fin) ∧
      s'.mem = s0.mem ∧ CalleeSaved s0 s' := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hx8 hacc hmem
  subst hpc
  have hld := ro_readU8 regs.x8 hro off (by omega) hx8
  mc_step_ex_with step_hwLoop hc 94 hwLoopInsn [hld]
  mc_step_ex step_hwLoop hc 95 hwLoopInsn
  mc_step_ex step_hwLoop hc 96 hwLoopInsn
  refine ⟨0, _, Arm64.run_zero _ _, hcs.x30, ?_, hmem,
    ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
     hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
     hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩⟩
  rw [rawExtend_u8_fin data off fin (by omega) hfin acc, Crc32c.bytes_of_le data (by omega)]
  simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
  rw [hacc]
  rfl

/-- Shared 2-byte + optional 1-byte exit (`idx = 81..85`, `L.hwLoopBase + 324`), used by `r ∈ {6, 7, 10, 11}`. -/
private theorem hwLoop_exit_81 {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s0 s : Arm64.ArmState} {objPtr : UInt64} {data : ByteArray}
    (hs : data.size < USize.size) {off fin : Nat} {acc : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) data)
    (hpc : s.pc = L.hwLoopBase + 324)
    (hx8 : s.regs.x8 = objPtr + 0x18)
    (hx11 : s.regs.x11 = (off + 2).toUInt64)
    (hx2 : s.regs.x2 = fin.toUInt64)
    (hlo : off + 2 ≤ fin)
    (hhi : fin ≤ off + 3)
    (hfin : fin ≤ data.size)
    (hw9 : (s.getW r9).toUInt16 = Crc32c.word16 (data[off]'(by omega)) (data[off + 1]'(by omega)))
    (hacc : s.getW r3 = acc)
    (hmem : s.mem = s0.mem)
    (hcs : CalleeSaved s0 s) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s0.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes data off fin) ∧
      s'.mem = s0.mem ∧ CalleeSaved s0 s' := by
  have hus := usize_le_2pow64
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hx8 hx11 hx2 hw9 hacc hmem
  subst hpc
  rw [rawExtend_u16_fin data hs off fin hlo hfin acc]
  mc_step_ex step_hwLoop hc 81 hwLoopInsn
  mc_step_ex step_hwLoop hc 82 hwLoopInsn
  by_cases heven : fin = off + 2
  · have hb83 : regs.x2 ≤ regs.x11 := by
      rw [hx2, hx11, u64_le_iff_nat (by omega) (by omega)]; omega
    mc_step_ex_with step_hwLoop hc 83 hwLoopInsn [hb83]
    refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
      ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
       hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
       hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
    simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hw9 hacc ⊢
    rw [hacc, hw9]
  · have hb83 : ¬ (regs.x2 ≤ regs.x11) := by
      rw [hx2, hx11, u64_le_iff_nat (by omega) (by omega)]; omega
    mc_step_ex_with step_hwLoop hc 83 hwLoopInsn [hb83]
    mc_step_ex step_hwLoop hc 84 hwLoopInsn
    mc_step_ex step_hwLoop hc 85 hwLoopInsn
    refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
      ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
       hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
       hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
    · dsimp only; rw [hx8, hx11]
    · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hw9 hacc ⊢
      rw [hacc, hw9]

/-! ### `< 16 B` tail (`idx = 13..98`, `L.hwLoopBase + 52`) -/

private theorem hwLoop_tail {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s0 s : Arm64.ArmState} {objPtr : UInt64} {data : ByteArray}
    (hs : data.size < USize.size) {off fin : Nat} {acc : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) data)
    (hpc : s.pc = L.hwLoopBase + 52)
    (hx0 : s.regs.x0 = objPtr)
    (hx1 : s.regs.x1 = off.toUInt64)
    (hx2 : s.regs.x2 = fin.toUInt64)
    (hx8 : s.regs.x8 = (fin - off).toUInt64)
    (hacc : s.getW r3 = acc)
    (hle : off ≤ fin)
    (hlt16 : fin - off < 16)
    (hfin : fin ≤ data.size)
    (hmem : s.mem = s0.mem)
    (hcs : CalleeSaved s0 s) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s0.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes data off fin) ∧
      s'.mem = s0.mem ∧ CalleeSaved s0 s' := by
  have hus := usize_le_2pow64
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hx0 hx1 hx2 hx8 hacc hmem
  subst hpc
  mc_step_ex step_hwLoop hc 13 hwLoopInsn
  by_cases h8 : 8 ≤ fin - off
  · -- `r ∈ {8..15}`: `idx = 14 → 24..31`
    have hb14 : (7 : UInt64) < regs.x8 := by
      rw [hx8, lit_lt_toUInt64_7 (by omega)]; omega
    mc_step_ex_with step_hwLoop hc 14 hwLoopInsn [hb14]
    mc_step_ex step_hwLoop hc 24 hwLoopInsn
    mc_step_ex step_hwLoop hc 25 hwLoopInsn
    mc_step_ex step_hwLoop hc 26 hwLoopInsn
    have hld27 := ro_readU64 (regs.x0 + (0x18 + regs.x1)) hro hs off (by omega)
      (by rw [hx0, hx1]; ac_rfl)
    mc_step_ex_with step_hwLoop hc 27 hwLoopInsn [hld27]
    mc_step_ex step_hwLoop hc 28 hwLoopInsn
    mc_step_ex step_hwLoop hc 29 hwLoopInsn
    mc_step_ex step_hwLoop hc 30 hwLoopInsn
    rw [rawExtend_u64_fin data hs off fin (by omega) hfin acc]
    have hx11_8 : regs.x2 - (regs.x1 + 8) = (fin - (off + 8)).toUInt64 := by
      rw [hx2, hx1, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, ← nat_add_toUInt64]
      exact nat_sub_toUInt64 fin (off + 8) (by omega) (by omega)
    by_cases h12 : 12 ≤ fin - off
    · -- `r ∈ {12..15}`: `idx = 31 → 49..60`
      have hb31 : (3 : UInt64) < regs.x2 - (regs.x1 + 8) := by
        rw [hx11_8, lit_lt_toUInt64_3 (by omega)]; omega
      mc_step_ex_with step_hwLoop hc 31 hwLoopInsn [hb31]
      mc_step_ex step_hwLoop hc 49 hwLoopInsn
      have hld50 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 8))) hro (off + 8) (by omega)
        (by rw [hx0, hx1, nat_add_toUInt64]; ac_rfl)
      have hld51 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 9))) hro ((off + 8) + 1) (by omega)
        (by rw [hx0, hx1, show (off + 8) + 1 = off + 9 by omega, nat_add_toUInt64]; ac_rfl)
      have hld52 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 10))) hro ((off + 8) + 2) (by omega)
        (by rw [hx0, hx1, show (off + 8) + 2 = off + 10 by omega, nat_add_toUInt64]; ac_rfl)
      have hld55 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 11))) hro ((off + 8) + 3) (by omega)
        (by rw [hx0, hx1, show (off + 8) + 3 = off + 11 by omega, nat_add_toUInt64]; ac_rfl)
      mc_step_ex_with step_hwLoop hc 50 hwLoopInsn [hld50]
      mc_step_ex_with step_hwLoop hc 51 hwLoopInsn [hld51]
      mc_step_ex_with step_hwLoop hc 52 hwLoopInsn [hld52]
      mc_step_ex step_hwLoop hc 53 hwLoopInsn
      mc_step_ex step_hwLoop hc 54 hwLoopInsn
      mc_step_ex_with step_hwLoop hc 55 hwLoopInsn [hld55]
      mc_step_ex step_hwLoop hc 56 hwLoopInsn
      mc_step_ex step_hwLoop hc 57 hwLoopInsn
      mc_step_ex step_hwLoop hc 58 hwLoopInsn
      mc_step_ex step_hwLoop hc 59 hwLoopInsn
      rw [rawExtend_u32_fin data hs (off + 8) fin (by omega) hfin,
          show Crc32c.bytes data ((off + 8) + 4) fin = Crc32c.bytes data (off + 12) fin from rfl]
      have hx10_12 : regs.x2 - (regs.x1 + 12) = (fin - (off + 12)).toUInt64 := by
        rw [hx2, hx1, show (12 : UInt64) = (12 : Nat).toUInt64 from rfl, ← nat_add_toUInt64]
        exact nat_sub_toUInt64 fin (off + 12) (by omega) (by omega)
      by_cases h14 : 14 ≤ fin - off
      · -- `r ∈ {14, 15}`: `idx = 60 → 86..92`
        have hb60 : (1 : UInt64) < regs.x2 - (regs.x1 + 12) := by
          rw [hx10_12, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 60 hwLoopInsn [hb60]
        mc_step_ex step_hwLoop hc 86 hwLoopInsn
        have hld87 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 12))) hro (off + 12) (by omega)
          (by rw [hx0, hx1, nat_add_toUInt64]; ac_rfl)
        have hld88 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 13))) hro ((off + 12) + 1) (by omega)
          (by rw [hx0, hx1, show (off + 12) + 1 = off + 13 by omega, nat_add_toUInt64]; ac_rfl)
        mc_step_ex_with step_hwLoop hc 87 hwLoopInsn [hld87]
        mc_step_ex_with step_hwLoop hc 88 hwLoopInsn [hld88]
        mc_step_ex step_hwLoop hc 89 hwLoopInsn
        mc_step_ex step_hwLoop hc 90 hwLoopInsn
        mc_step_ex step_hwLoop hc 91 hwLoopInsn
        rw [rawExtend_u16_fin data hs (off + 12) fin (by omega) hfin,
            show Crc32c.bytes data ((off + 12) + 2) fin = Crc32c.bytes data (off + 14) fin from rfl]
        by_cases h15 : fin = off + 14
        · have hb92 : regs.x2 ≤ regs.x1 + 14 := by
            rw [hx2, hx1, show (14 : UInt64) = (14 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 92 hwLoopInsn [hb92]
          refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64,
            nat_toUInt32_8, toUInt16_reassemble2] at hacc ⊢
          rw [hacc]; rfl
        · have hb92 : ¬ (regs.x2 ≤ regs.x1 + 14) := by
            rw [hx2, hx1, show (14 : UInt64) = (14 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 92 hwLoopInsn [hb92]
          mc_step_ex step_hwLoop hc 93 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          · dsimp only; rw [hx0, hx1, nat_add_toUInt64]; ac_rfl
          · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64,
              nat_toUInt32_8, toUInt16_reassemble2] at hacc ⊢
            rw [hacc]; rfl
      · -- `r ∈ {12, 13}`: `idx = 60 → 61..63`
        have hb60 : ¬ ((1 : UInt64) < regs.x2 - (regs.x1 + 12)) := by
          rw [hx10_12, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 60 hwLoopInsn [hb60]
        mc_step_ex step_hwLoop hc 61 hwLoopInsn
        by_cases h12eq : fin = off + 12
        · have hb62 : regs.x2 ≤ regs.x1 + 12 := by
            rw [hx2, hx1, show (12 : UInt64) = (12 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 62 hwLoopInsn [hb62]
          refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]; rfl
        · have hb62 : ¬ (regs.x2 ≤ regs.x1 + 12) := by
            rw [hx2, hx1, show (12 : UInt64) = (12 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 62 hwLoopInsn [hb62]
          mc_step_ex step_hwLoop hc 63 hwLoopInsn
          mc_step_ex step_hwLoop hc 84 hwLoopInsn
          mc_step_ex step_hwLoop hc 85 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          · dsimp only; rw [hx0, hx1, nat_add_toUInt64]; ac_rfl
          · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
            rw [hacc]; rfl
    · -- `r ∈ {8..11}`: `idx = 31 → 32..36`
      have hb31 : ¬ ((3 : UInt64) < regs.x2 - (regs.x1 + 8)) := by
        rw [hx11_8, lit_lt_toUInt64_3 (by omega)]; omega
      mc_step_ex_with step_hwLoop hc 31 hwLoopInsn [hb31]
      mc_step_ex step_hwLoop hc 32 hwLoopInsn
      by_cases h10 : 10 ≤ fin - off
      · -- `r ∈ {10, 11}`: `idx = 33 → 72..76 → 81`
        have hb33 : (1 : UInt64) < regs.x2 - (regs.x1 + 8) := by
          rw [hx11_8, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 33 hwLoopInsn [hb33]
        mc_step_ex step_hwLoop hc 72 hwLoopInsn
        have hld73 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 8))) hro (off + 8) (by omega)
          (by rw [hx0, hx1, nat_add_toUInt64]; ac_rfl)
        have hld74 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 9))) hro ((off + 8) + 1) (by omega)
          (by rw [hx0, hx1, show (off + 8) + 1 = off + 9 by omega, nat_add_toUInt64]; ac_rfl)
        mc_step_ex_with step_hwLoop hc 73 hwLoopInsn [hld73]
        mc_step_ex_with step_hwLoop hc 74 hwLoopInsn [hld74]
        mc_step_ex step_hwLoop hc 75 hwLoopInsn
        mc_step_ex step_hwLoop hc 76 hwLoopInsn
        refine hwLoop_exit_81 hs hc hro rfl
          (by dsimp only; rw [hx0])
          (by dsimp only; rw [hx1, show (off + 8) + 2 = off + 10 by omega, nat_add_toUInt64]; rfl)
          hx2 (by omega) (by omega) hfin ?_ ?_ hmem
          ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
           hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
           hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
        · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64,
            nat_toUInt32_8, toUInt16_reassemble2]
        · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]
      · -- `r ∈ {8, 9}`: `idx = 33 → 34..36`
        have hb33 : ¬ ((1 : UInt64) < regs.x2 - (regs.x1 + 8)) := by
          rw [hx11_8, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 33 hwLoopInsn [hb33]
        mc_step_ex step_hwLoop hc 34 hwLoopInsn
        by_cases h9 : fin = off + 9
        · have hb35 : regs.x1 + 8 < regs.x2 := by
            rw [hx1, hx2, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_lt_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 35 hwLoopInsn [hb35]
          mc_step_ex step_hwLoop hc 93 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          · dsimp only; rw [hx0, hx1, nat_add_toUInt64]; ac_rfl
          · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
            rw [hacc]
        · have hb35 : ¬ (regs.x1 + 8 < regs.x2) := by
            rw [hx1, hx2, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_lt_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 35 hwLoopInsn [hb35]
          mc_step_ex step_hwLoop hc 36 hwLoopInsn
          refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]
  · -- `r ∈ {0..7}`: `idx = 14 → 15..20`
    have hb14 : ¬ ((7 : UInt64) < regs.x8) := by
      rw [hx8, lit_lt_toUInt64_7 (by omega)]; omega
    mc_step_ex_with step_hwLoop hc 14 hwLoopInsn [hb14]
    mc_step_ex step_hwLoop hc 15 hwLoopInsn
    by_cases h4 : 4 ≤ fin - off
    · -- `r ∈ {4..7}`: `idx = 16 → 37..44`
      have hb16 : (3 : UInt64) < regs.x8 := by
        rw [hx8, lit_lt_toUInt64_3 (by omega)]; omega
      mc_step_ex_with step_hwLoop hc 16 hwLoopInsn [hb16]
      mc_step_ex step_hwLoop hc 37 hwLoopInsn
      mc_step_ex step_hwLoop hc 38 hwLoopInsn
      mc_step_ex step_hwLoop hc 39 hwLoopInsn
      have hld40 := ro_readU32 (regs.x0 + (0x18 + regs.x1)) hro off (by omega)
        (by rw [hx0, hx1]; ac_rfl)
      mc_step_ex_with step_hwLoop hc 40 hwLoopInsn [hld40]
      mc_step_ex step_hwLoop hc 41 hwLoopInsn
      mc_step_ex step_hwLoop hc 42 hwLoopInsn
      mc_step_ex step_hwLoop hc 43 hwLoopInsn
      rw [rawExtend_u32_fin data hs off fin (by omega) hfin acc]
      have hx11_4 : regs.x2 - (regs.x1 + 4) = (fin - (off + 4)).toUInt64 := by
        rw [hx2, hx1, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, ← nat_add_toUInt64]
        exact nat_sub_toUInt64 fin (off + 4) (by omega) (by omega)
      by_cases h6 : 6 ≤ fin - off
      · -- `r ∈ {6, 7}`: `idx = 44 → 77..80 → 81`
        have hb44 : (1 : UInt64) < regs.x2 - (regs.x1 + 4) := by
          rw [hx11_4, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 44 hwLoopInsn [hb44]
        mc_step_ex step_hwLoop hc 77 hwLoopInsn
        have hld78 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 4))) hro (off + 4) (by omega)
          (by rw [hx0, hx1, nat_add_toUInt64]; ac_rfl)
        have hld79 := ro_readU8 (regs.x0 + (0x18 + (regs.x1 + 5))) hro ((off + 4) + 1) (by omega)
          (by rw [hx0, hx1, show (off + 4) + 1 = off + 5 by omega, nat_add_toUInt64]; ac_rfl)
        mc_step_ex_with step_hwLoop hc 78 hwLoopInsn [hld78]
        mc_step_ex_with step_hwLoop hc 79 hwLoopInsn [hld79]
        mc_step_ex step_hwLoop hc 80 hwLoopInsn
        refine hwLoop_exit_81 hs hc hro rfl
          (by dsimp only; rw [hx0])
          (by dsimp only; rw [hx1, show (off + 4) + 2 = off + 6 by omega, nat_add_toUInt64]; rfl)
          hx2 (by omega) (by omega) hfin ?_ ?_ hmem
          ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
           hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
           hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
        · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64,
            nat_toUInt32_8, toUInt16_reassemble2]
        · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]
      · -- `r ∈ {4, 5}`: `idx = 44 → 45..48`
        have hb44 : ¬ ((1 : UInt64) < regs.x2 - (regs.x1 + 4)) := by
          rw [hx11_4, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 44 hwLoopInsn [hb44]
        mc_step_ex step_hwLoop hc 45 hwLoopInsn
        by_cases h4eq : fin = off + 4
        · have hb46 : regs.x2 ≤ regs.x1 + 4 := by
            rw [hx2, hx1, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 46 hwLoopInsn [hb46]
          refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]
        · have hb46 : ¬ (regs.x2 ≤ regs.x1 + 4) := by
            rw [hx2, hx1, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 46 hwLoopInsn [hb46]
          mc_step_ex step_hwLoop hc 47 hwLoopInsn
          mc_step_ex step_hwLoop hc 48 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          · dsimp only; rw [hx0, hx1, nat_add_toUInt64]; ac_rfl
          · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
            rw [hacc]
    · -- `r ∈ {0..3}`: `idx = 16 → 17..23`
      have hb16 : ¬ ((3 : UInt64) < regs.x8) := by
        rw [hx8, lit_lt_toUInt64_3 (by omega)]; omega
      mc_step_ex_with step_hwLoop hc 16 hwLoopInsn [hb16]
      mc_step_ex step_hwLoop hc 17 hwLoopInsn
      by_cases h2 : 2 ≤ fin - off
      · -- `r ∈ {2, 3}`: `idx = 18 → 64..71`
        have hb18 : (1 : UInt64) < regs.x8 := by
          rw [hx8, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 18 hwLoopInsn [hb18]
        mc_step_ex step_hwLoop hc 64 hwLoopInsn
        mc_step_ex step_hwLoop hc 65 hwLoopInsn
        have hld66 := ro_readU16 (regs.x0 + (0x18 + regs.x1)) hro off (by omega)
          (by rw [hx0, hx1]; ac_rfl)
        mc_step_ex_with step_hwLoop hc 66 hwLoopInsn [hld66]
        mc_step_ex step_hwLoop hc 67 hwLoopInsn
        mc_step_ex step_hwLoop hc 68 hwLoopInsn
        rw [rawExtend_u16_fin data hs off fin (by omega) hfin acc]
        by_cases h2eq : fin = off + 2
        · have hb69 : regs.x2 ≤ regs.x1 + 2 := by
            rw [hx2, hx1, show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 69 hwLoopInsn [hb69]
          refine hwLoop_exit_even hc rfl ?_ (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
          rw [hacc]
        · have hb69 : ¬ (regs.x2 ≤ regs.x1 + 2) := by
            rw [hx2, hx1, show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, ← nat_add_toUInt64,
                u64_le_iff_nat (by omega) (by omega)]
            omega
          mc_step_ex_with step_hwLoop hc 69 hwLoopInsn [hb69]
          mc_step_ex step_hwLoop hc 70 hwLoopInsn
          mc_step_ex step_hwLoop hc 71 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ ?_ (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          · dsimp only; rw [hx0, hx1, nat_add_toUInt64]; ac_rfl
          · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
            rw [hacc]
      · -- `r ∈ {0, 1}`: `idx = 18 → 19..23`
        have hb18 : ¬ ((1 : UInt64) < regs.x8) := by
          rw [hx8, lit_lt_toUInt64_1 (by omega)]; omega
        mc_step_ex_with step_hwLoop hc 18 hwLoopInsn [hb18]
        mc_step_ex step_hwLoop hc 19 hwLoopInsn
        by_cases h0eq : fin = off
        · have hb20 : regs.x2 ≤ regs.x1 := by
            rw [hx2, hx1, u64_le_iff_nat (by omega) (by omega)]; omega
          mc_step_ex_with step_hwLoop hc 20 hwLoopInsn [hb20]
          exact hwLoop_exit_even hc rfl hacc (by omega) hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
        · have hb20 : ¬ (regs.x2 ≤ regs.x1) := by
            rw [hx2, hx1, u64_le_iff_nat (by omega) (by omega)]; omega
          mc_step_ex_with step_hwLoop hc 20 hwLoopInsn [hb20]
          mc_step_ex step_hwLoop hc 21 hwLoopInsn
          mc_step_ex step_hwLoop hc 22 hwLoopInsn
          mc_step_ex step_hwLoop hc 23 hwLoopInsn
          refine hwLoop_exit_odd hc hro rfl ?_ hacc (by omega) hfin hmem
            ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
             hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
             hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
          dsimp only; rw [hx0, hx1]; ac_rfl

/-! ### 16-byte-per-iteration inner loop (`idx = 5..12`, `L.hwLoopBase + 20`) -/

private theorem hwLoop_body {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s0 : Arm64.ArmState} {objPtr : UInt64} {data : ByteArray}
    (hs : data.size < USize.size) {fin : Nat} (hfin : fin ≤ data.size) :
    ∀ (rem : Nat) (s : Arm64.ArmState) (off : Nat) (acc : UInt32),
      CodeLoaded code s.mem L →
      s.mem.hasROBytes (objPtr + 0x18) data →
      s.pc = L.hwLoopBase + 20 →
      s.regs.x0 = objPtr →
      s.regs.x1 = off.toUInt64 →
      s.regs.x2 = fin.toUInt64 →
      s.regs.x8 = (fin - off).toUInt64 →
      s.regs.x9 = (objPtr + 0x18) + (off + 8).toUInt64 →
      s.getW r3 = acc →
      fin - off = rem →
      16 ≤ rem →
      s.mem = s0.mem →
      CalleeSaved s0 s →
      ∃ k s', Arm64.run code k s = some s' ∧
        s'.pc = s0.regs.x30 ∧
        s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes data off fin) ∧
        s'.mem = s0.mem ∧ CalleeSaved s0 s' := by
  have hus := usize_le_2pow64
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s off acc hc hro hpc hx0 hx1 hx2 hx8 hx9 hacc hrem h16 hmem hcs
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hc hro hpc hx0 hx1 hx2 hx8 hx9 hacc hmem
    subst hpc
    have hld1 := ro_readU64 (regs.x9 + 0xfffffffffffffff8) hro hs off (by omega) (by
      rw [hx9, nat_add_toUInt64 off 8, show (8 : Nat).toUInt64 = (8 : UInt64) from rfl]
      have hsub := add_neg8_cancel ((objPtr + 0x18) + off.toUInt64)
      simp only [UInt64.add_assoc] at hsub ⊢
      exact hsub)
    have hld2 := ro_readU64 (regs.x9 + (0xfffffffffffffff8 + 8)) hro hs (off + 8) (by omega) (by
      have hz : (0xfffffffffffffff8 : UInt64) + 8 = 0 := rfl
      rw [hz, UInt64.add_zero, hx9])
    rw [rawExtend_u64_fin data hs off fin (by omega) hfin acc,
        rawExtend_u64_fin data hs (off + 8) fin (by omega) hfin,
        show Crc32c.bytes data ((off + 8) + 8) fin = Crc32c.bytes data (off + 16) fin from rfl]
    mc_step_ex step_hwLoop hc 5 hwLoopInsn
    mc_step_ex_with step_hwLoop hc 6 hwLoopInsn [hld1, hld2]
    mc_step_ex step_hwLoop hc 7 hwLoopInsn
    mc_step_ex step_hwLoop hc 8 hwLoopInsn
    mc_step_ex step_hwLoop hc 9 hwLoopInsn
    mc_step_ex step_hwLoop hc 10 hwLoopInsn
    mc_step_ex step_hwLoop hc 11 hwLoopInsn
    have hx8' : regs.x8 - 16 = (fin - (off + 16)).toUInt64 := by
      rw [hx8, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
          nat_sub_toUInt64 (fin - off) 16 (by omega) (by omega)]
      rfl
    by_cases hmore : 16 ≤ fin - (off + 16)
    · have hb12 : (16 : UInt64) ≤ regs.x8 - 16 := by
        rw [hx8', lit_le_toUInt64_16 (by omega)]; exact hmore
      mc_step_ex_with step_hwLoop hc 12 hwLoopInsn [hb12]
      refine ih (fin - (off + 16)) (by omega) _ (off + 16) _ hc hro ?_ hx0 ?_ hx2 hx8' ?_ ?_ rfl hmore hmem
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
      · dsimp only
        have hpc_off : (20 : UInt64) + (4 + (4 + (4 + (4 + (4 + (4 + (4 + 0xffffffffffffffe4))))))) = 20 := rfl
        rw [hpc_off]
      · dsimp only; rw [hx1, nat_add_toUInt64]; rfl
      · dsimp only
        rw [hx9, show (off + 16) + 8 = (off + 8) + 16 by omega,
            nat_add_toUInt64 (off + 8) 16, show (16 : Nat).toUInt64 = (16 : UInt64) from rfl]
        ac_rfl
      · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
        rw [hacc]
    · have hb12 : ¬ ((16 : UInt64) ≤ regs.x8 - 16) := by
        rw [hx8', lit_le_toUInt64_16 (by omega)]; exact hmore
      mc_step_ex_with step_hwLoop hc 12 hwLoopInsn [hb12]
      refine hwLoop_tail hs hc hro ?_ hx0 ?_ hx2 hx8' ?_ (by omega) (by omega) hfin hmem
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
      · dsimp only
        have hpc_off : (20 : UInt64) + (4 + (4 + (4 + (4 + (4 + (4 + (4 + 4))))))) = 52 := rfl
        rw [hpc_off]
      · dsimp only; rw [hx1, nat_add_toUInt64]; rfl
      · simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64] at hacc ⊢
        rw [hacc]

/-! ### Exported machine-code specification: `hwLoop_mc_spec` -/

/-- Machine-code specification of `_lp_leanmemcpy_Crc32c_hwLoop___redArg`:
executes from `L.hwLoopBase` to caller return address `s.regs.x30`, placing
`Crc32c.rawExtend s0 (Crc32c.bytes data i.toNat fin.toNat)` in `W0`, with zero stack
writes (`s'.mem = s.mem`), guard-page safety (only `[objPtr + 0x18, objPtr + 0x18 + data.size)`
needs `.ro` permission), and full AAPCS64 register preservation (`CalleeSaved s s'`). -/
theorem hwLoop_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {data : ByteArray}
    (hs : data.size < USize.size) {i fin : USize}
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ data.size) {s0 : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) data)
    (hpc : s.pc = L.hwLoopBase)
    (hx0 : s.regs.x0 = objPtr)
    (hx1 : s.regs.x1 = i.toUInt64)
    (hx2 : s.regs.x2 = fin.toUInt64)
    (hs0 : s.getW r3 = s0) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend s0 (Crc32c.bytes data i.toNat fin.toNat) ∧
      s'.mem = s.mem ∧
      CalleeSaved s s' := by
  have hus := usize_le_2pow64
  have hi64 : i.toUInt64 = i.toNat.toUInt64 :=
    u64_ext (by rw [USize.toNat_toUInt64, nat_toUInt64_toNat i.toNat (by omega)])
  have hfin64 : fin.toUInt64 = fin.toNat.toUInt64 :=
    u64_ext (by rw [USize.toNat_toUInt64, nat_toUInt64_toNat fin.toNat (by omega)])
  rw [hi64] at hx1
  rw [hfin64] at hx2
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hx0 hx1 hx2 hs0 ⊢
  subst hpc
  let sInit : Arm64.ArmState := { regs, sp, simd, nzcv, pc := L.hwLoopBase, mem }
  have hx8_sub : regs.x2 - regs.x1 = (fin.toNat - i.toNat).toUInt64 := by
    rw [hx2, hx1]
    exact nat_sub_toUInt64 fin.toNat i.toNat hi (by omega)
  mc_step_ex step_hwLoop hc 0 hwLoopInsn
  mc_step_ex step_hwLoop hc 1 hwLoopInsn
  by_cases hlt : fin.toNat - i.toNat < 16
  · have hb2 : regs.x2 - regs.x1 < 16 := by
      rw [hx8_sub, toUInt64_lt_16 (by omega)]; exact hlt
    mc_step_ex_with step_hwLoop hc 2 hwLoopInsn [hb2]
    exact hwLoop_tail (s0 := sInit) hs hc hro rfl hx0 hx1 hx2 hx8_sub hs0 hi hlt hfin rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hb2 : ¬ (regs.x2 - regs.x1 < 16) := by
      rw [hx8_sub, toUInt64_lt_16 (by omega)]; exact hlt
    mc_step_ex_with step_hwLoop hc 2 hwLoopInsn [hb2]
    mc_step_ex step_hwLoop hc 3 hwLoopInsn
    mc_step_ex step_hwLoop hc 4 hwLoopInsn
    refine hwLoop_body (s0 := sInit) hs hfin (fin.toNat - i.toNat) _ i.toNat s0
      hc hro rfl hx0 hx1 hx2 hx8_sub ?_ hs0 rfl (by omega) rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    dsimp only
    rw [hx1, hx0, nat_add_toUInt64 i.toNat 8,
        show (0x20 : UInt64) = 0x18 + (8 : Nat).toUInt64 from rfl]
    ac_rfl

end Crc32c.Arm64MC
