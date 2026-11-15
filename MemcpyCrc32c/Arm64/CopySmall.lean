/-
Machine-code verification of `leancrc32c_copy_small` (48 instructions,
hand-written in `cxx/leancrc32c_copy_arm64.S`): copying `1 ≤ n ≤ 64` bytes
between non-overlapping buffers and returning the CRC it was handed.
-/
import MemcpyCrc32c.Arm64.Copy

namespace Crc32c.Arm64MC
open SimdModels
open Copy

/-! ### Code bytes, decoded instructions, and the fetch/decode certificate -/

def copySmallWords : Array UInt32 := #[
  0x8b020024, 0x8b020005, 0xf100405f, 0x540001e3, 0xf100805f, 0x540000e8, 0xa9401c26, 0xa97f2488,
  0xa9001c06, 0xa93f24a8, 0x2a0303e0, 0xd65f03c0, 0xad400420, 0xad7f0c82, 0xad000400, 0xad3f0ca2,
  0x2a0303e0, 0xd65f03c0, 0xf100205f, 0x540000e3, 0x29401c26, 0x297f2488, 0x29001c06, 0x293f24a8,
  0x2a0303e0, 0xd65f03c0, 0xf100105f, 0x54000123, 0xb9400026, 0xd1001088, 0xb9400107, 0xb9000006,
  0xd10010a9, 0xb9000127, 0x2a0303e0, 0xd65f03c0, 0xd341fc49, 0x39400026, 0x38696827, 0xd1000488,
  0x39400108, 0x39000006, 0x8b09000a, 0x39000147, 0xd10004ab, 0x39000168, 0x2a0303e0, 0xd65f03c0]

theorem copySmallWords_size : copySmallWords.size = 48 := rfl

def copySmallInsn (idx : Nat) : Arm64.Instr :=
  if idx < 24 then
    if idx < 12 then
      if idx < 6 then
        if idx < 3 then
          if idx < 2 then
            if idx < 1 then
              .addSubReg true false false .lsl r4 r1 r2 0
            else
              .addSubReg true false false .lsl r5 r0 r2 0
          else
            .addSubImm true true true r31 r2 0x10
        else
          if idx < 5 then
            if idx < 4 then
              .bCond c3 0x3c
            else
              .addSubImm true true true r31 r2 0x20
          else
            .bCond c8 0x1c
      else
        if idx < 9 then
          if idx < 8 then
            if idx < 7 then
              .ldpGP true .signedOffset r6 r7 r1 0
            else
              .ldpGP true .signedOffset r8 r9 r4 0xfffffffffffffff0
          else
            .stpGP true .signedOffset r6 r7 r0 0
        else
          if idx < 11 then
            if idx < 10 then
              .stpGP true .signedOffset r8 r9 r5 0xfffffffffffffff0
            else
              .logicReg false .orrOp .lsl false r0 r31 r3 0
          else
            .ret r30
    else
      if idx < 18 then
        if idx < 15 then
          if idx < 14 then
            if idx < 13 then
              .ldpQ .signedOffset r0 r1 r1 0
            else
              .ldpQ .signedOffset r2 r3 r4 0xffffffffffffffe0
          else
            .stpQ .signedOffset r0 r1 r0 0
        else
          if idx < 17 then
            if idx < 16 then
              .stpQ .signedOffset r2 r3 r5 0xffffffffffffffe0
            else
              .logicReg false .orrOp .lsl false r0 r31 r3 0
          else
            .ret r30
      else
        if idx < 21 then
          if idx < 20 then
            if idx < 19 then
              .addSubImm true true true r31 r2 0x8
            else
              .bCond c3 0x1c
          else
            .ldpGP false .signedOffset r6 r7 r1 0
        else
          if idx < 23 then
            if idx < 22 then
              .ldpGP false .signedOffset r8 r9 r4 0xfffffffffffffff8
            else
              .stpGP false .signedOffset r6 r7 r0 0
          else
            .stpGP false .signedOffset r8 r9 r5 0xfffffffffffffff8
  else
    if idx < 36 then
      if idx < 30 then
        if idx < 27 then
          if idx < 26 then
            if idx < 25 then
              .logicReg false .orrOp .lsl false r0 r31 r3 0
            else
              .ret r30
          else
            .addSubImm true true true r31 r2 0x4
        else
          if idx < 29 then
            if idx < 28 then
              .bCond c3 0x24
            else
              .ldrUImm .w32 r6 r1 0
          else
            .addSubImm true true false r8 r4 0x4
      else
        if idx < 33 then
          if idx < 32 then
            if idx < 31 then
              .ldrUImm .w32 r7 r8 0
            else
              .strUImm .w32 r6 r0 0
          else
            .addSubImm true true false r9 r5 0x4
        else
          if idx < 35 then
            if idx < 34 then
              .strUImm .w32 r7 r9 0
            else
              .logicReg false .orrOp .lsl false r0 r31 r3 0
          else
            .ret r30
    else
      if idx < 42 then
        if idx < 39 then
          if idx < 38 then
            if idx < 37 then
              .ubfm true r9 r2 1 63
            else
              .ldrUImm .b8 r6 r1 0
          else
            .ldrReg .b8 r7 r1 r9
        else
          if idx < 41 then
            if idx < 40 then
              .addSubImm true true false r8 r4 0x1
            else
              .ldrUImm .b8 r8 r8 0
          else
            .strUImm .b8 r6 r0 0
      else
        if idx < 45 then
          if idx < 44 then
            if idx < 43 then
              .addSubReg true false false .lsl r10 r0 r9 0
            else
              .strUImm .b8 r7 r10 0
          else
            .addSubImm true true false r11 r5 0x1
        else
          if idx < 47 then
            if idx < 46 then
              .strUImm .b8 r8 r11 0
            else
              .logicReg false .orrOp .lsl false r0 r31 r3 0
          else
            .ret r30

set_option maxRecDepth 8192 in
private theorem copySmall_decode_ok :
    checkWordsAux copySmallWords copySmallInsn 48 = true := rfl

/-- The 48 instruction words of `leancrc32c_copy_small` are loaded at `base`. -/
def CopySmallLoaded (code : UInt64 → Option UInt32) (base : UInt64) : Prop :=
  ∀ idx (h : idx < copySmallWords.size),
    code (base + (4 * idx).toUInt64) = some copySmallWords[idx]

theorem step_copySmall {code : UInt64 → Option UInt32} {base : UInt64}
    (hc : CopySmallLoaded code base) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = base + (4 * idx).toUInt64)
    (hok : decide (idx < 48) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (copySmallInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < copySmallWords.size := by rw [copySmallWords_size]; exact hp
  have hfetch := hc idx hsz
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch
    (checkWordsAux_spec copySmallWords copySmallInsn 48 copySmall_decode_ok idx hsz hp)

/-! ### Load and store facts at explicit addresses -/

section
variable {m0 : Arm64.Mem} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}

theorem load8' (h : Setup m0 src dst b n) {w off : Nat} (hw : w ≤ n) (ho : off + 8 ≤ n)
    {a : UInt64} (ha : a = src + off.toUInt64) :
    (patch m0 dst b w).readU64LE a = some (w8 b off) := by
  rw [ha]; exact Copy.load8 h hw ho

theorem store8' (h : Setup m0 src dst b n) {w w' off : Nat} (how : off ≤ w) (ho : off + 8 ≤ n)
    (hw' : w' = max w (off + 8)) {a : UInt64} (ha : a = dst + off.toUInt64) :
    (patch m0 dst b w).writeU64LE a (w8 b off) = some (patch m0 dst b w') := by
  rw [ha, hw']; exact Copy.store8 h how ho

theorem load4' (h : Setup m0 src dst b n) {w off : Nat} (hw : w ≤ n) (ho : off + 4 ≤ n)
    {a : UInt64} (ha : a = src + off.toUInt64) :
    (patch m0 dst b w).readU32LE a = some (w4 b off) := by
  rw [ha]; exact Copy.load4 h hw ho

theorem store4' (h : Setup m0 src dst b n) {w w' off : Nat} (how : off ≤ w) (ho : off + 4 ≤ n)
    (hw' : w' = max w (off + 4)) {a : UInt64} (ha : a = dst + off.toUInt64) :
    (patch m0 dst b w).writeU32LE a (w4 b off) = some (patch m0 dst b w') := by
  rw [ha, hw']; exact Copy.store4 h how ho

theorem load1' (h : Setup m0 src dst b n) {w off : Nat} (hw : w ≤ n) (ho : off < n)
    {a : UInt64} (ha : a = src + off.toUInt64) :
    (patch m0 dst b w).readU8 a = some (b off) := by
  rw [ha]; exact Copy.patch_read h hw ho

theorem store1' (h : Setup m0 src dst b n) {w w' off : Nat} (how : off ≤ w) (ho : off + 1 ≤ n)
    (hw' : w' = max w (off + 1)) {a : UInt64} (ha : a = dst + off.toUInt64) :
    (patch m0 dst b w).writeU8 a (b off) = some (patch m0 dst b w') := by
  rw [ha, hw']; exact Copy.store1 h how ho

end

/-! ### The five size classes -/

theorem copySmall_mc_core {code : UInt64 → Option UInt32} {base : UInt64}
    {s : Arm64.ArmState} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hc : CopySmallLoaded code base) (hset : Setup s.mem src dst b n)
    (hn1 : 1 ≤ n) (hn64 : n ≤ 64)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = dst) (hx1 : s.regs.x1 = src)
    (hx2 : s.regs.x2 = n.toUInt64) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s.regs.x30 ∧ s'.mem = patch s.mem dst b n ∧
      s'.getW r0 = s.getW r3 ∧ CalleeSaved s s' := by
  have hd := hset.hd
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hset hpc hx0 hx1 hx2 ⊢
  subst hpc
  have p0 := patch_zero mem dst b
  have hx2n : regs.x2.toNat = n := by rw [hx2]; exact nat_toUInt64_toNat n (by omega)
  have a0 : regs.x1 = src + (0 : Nat).toUInt64 := by rw [hx1]; simp [Nat.toUInt64]
  have d0 : regs.x0 = dst + (0 : Nat).toUInt64 := by rw [hx0]; simp [Nat.toUInt64]
  have hcs0 : CalleeSaved
      ({ regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem } : Arm64.ArmState)
      ({ regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem } : Arm64.ArmState) :=
    CalleeSaved.refl _
  mc_step_ex step_copySmall hc 0 copySmallInsn
  mc_step_ex step_copySmall hc 1 copySmallInsn
  mc_step_ex step_copySmall hc 2 copySmallInsn
  by_cases h16 : n < 16
  · have hb3 : regs.x2 < 16 := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h16
    mc_step_ex_with step_copySmall hc 3 copySmallInsn [hb3]
    mc_step_ex step_copySmall hc 18 copySmallInsn
    by_cases h8 : n < 8
    · have hb19 : regs.x2 < 8 := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h8
      mc_step_ex_with step_copySmall hc 19 copySmallInsn [hb19]
      mc_step_ex step_copySmall hc 26 copySmallInsn
      by_cases h4 : n < 4
      · have hb27 : regs.x2 < 4 := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h4
        mc_step_ex_with step_copySmall hc 27 copySmallInsn [hb27]
        have hm : regs.x2 >>> 1 = (n / 2).toUInt64 := by
          apply Copy.u64_ext
          rw [UInt64.toNat_shiftRight, hx2n, nat_toUInt64_toNat _ (by omega)]
          simp [Nat.shiftRight_eq_div_pow]
        have h1 : Nat.toUInt64 1 = 1 := rfl
        have l1 := load1' hset (w := 0) (off := 0) (by omega) (by omega) a0
        have l2 := load1' hset (w := 0) (off := n / 2) (a := regs.x1 + (regs.x2 >>> 1)) (by omega)
          (by omega) (by rw [hx1, hm])
        have l3 := load1' hset (w := 0) (off := n - 1) (a := regs.x1 + regs.x2 - 1) (by omega) (by omega)
          (by rw [hx1, hx2]; exact copy_sub_addr' src n 1 (by omega))
        have s1 := store1' hset (w := 0) (w' := 1) (off := 0) (by omega) (by omega) (by omega) d0
        have s2 := store1' hset (w := 1) (w' := max 1 (n / 2 + 1)) (off := n / 2)
          (a := regs.x0 + (regs.x2 >>> 1)) (by omega) (by omega) rfl (by rw [hx0, hm])
        have s3 := store1' hset (w := max 1 (n / 2 + 1)) (w' := n) (off := n - 1)
          (a := regs.x0 + regs.x2 - 1) (by omega) (by omega) (by omega)
          (by rw [hx0, hx2]; exact copy_sub_addr' dst n 1 (by omega))
        rw [p0] at l1 l2 l3 s1
        mc_step_ex step_copySmall hc 36 copySmallInsn
        mc_step_ex_with step_copySmall hc 37 copySmallInsn [l1]
        mc_step_ex_with step_copySmall hc 38 copySmallInsn [l2, h1]
        mc_step_ex step_copySmall hc 39 copySmallInsn
        mc_step_ex_with step_copySmall hc 40 copySmallInsn [l3]
        mc_step_ex_with step_copySmall hc 41 copySmallInsn [s1]
        mc_step_ex step_copySmall hc 42 copySmallInsn
        mc_step_ex_with step_copySmall hc 43 copySmallInsn [s2, h1]
        mc_step_ex step_copySmall hc 44 copySmallInsn
        mc_step_ex_with step_copySmall hc 45 copySmallInsn [s3]
        mc_step_ex step_copySmall hc 46 copySmallInsn
        mc_step_ex step_copySmall hc 47 copySmallInsn
        refine ⟨0, _, Arm64.run_zero _ _, rfl, rfl, ?_,
          ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
           hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
           hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩⟩
        simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]
      · have hb27 : ¬ (regs.x2 < 4) := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h4
        mc_step_ex_with step_copySmall hc 27 copySmallInsn [hb27]
        have l1 := load4' hset (w := 0) (off := 0) (by omega) (by omega) a0
        have l2 := load4' hset (w := 0) (off := n - 4) (a := regs.x1 + regs.x2 - 4) (by omega) (by omega)
          (by rw [hx1, hx2]; exact copy_sub_addr' src n 4 (by omega))
        have s1 := store4' hset (w := 0) (w' := 4) (off := 0) (by omega) (by omega) (by omega) d0
        have s2 := store4' hset (w := 4) (w' := n) (off := n - 4) (a := regs.x0 + regs.x2 - 4)
          (by omega) (by omega) (by omega) (by rw [hx0, hx2]; exact copy_sub_addr' dst n 4 (by omega))
        rw [p0] at l1 l2 s1
        mc_step_ex_with step_copySmall hc 28 copySmallInsn [l1]
        mc_step_ex step_copySmall hc 29 copySmallInsn
        mc_step_ex_with step_copySmall hc 30 copySmallInsn [l2]
        mc_step_ex_with step_copySmall hc 31 copySmallInsn [s1]
        mc_step_ex step_copySmall hc 32 copySmallInsn
        mc_step_ex_with step_copySmall hc 33 copySmallInsn [s2]
        mc_step_ex step_copySmall hc 34 copySmallInsn
        mc_step_ex step_copySmall hc 35 copySmallInsn
        refine ⟨0, _, Arm64.run_zero _ _, rfl, rfl, ?_,
          ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
           hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
           hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩⟩
        simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]
    · have hb19 : ¬ (regs.x2 < 8) := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h8
      mc_step_ex_with step_copySmall hc 19 copySmallInsn [hb19]
      have z4 : (0 : UInt64) + 4 = 4 := rfl
      have l1 := load4' hset (w := 0) (off := 0) (by omega) (by omega) a0
      have l2 := load4' hset (w := 0) (off := 4) (a := regs.x1 + 4) (by omega) (by omega)
        (by rw [hx1]; rfl)
      have l3 := load4' hset (w := 0) (off := n - 8)
        (a := regs.x1 + (regs.x2 + 0xfffffffffffffff8)) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 8 (by omega))
      have l4 := load4' hset (w := 0) (off := n - 4)
        (a := regs.x1 + (regs.x2 + (0xfffffffffffffff8 + 4))) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 4 (by omega))
      have s1 := store4' hset (w := 0) (w' := 4) (off := 0) (by omega) (by omega) (by omega) d0
      have s2 := store4' hset (w := 4) (w' := 8) (off := 4) (a := regs.x0 + 4) (by omega)
        (by omega) (by omega) (by rw [hx0]; rfl)
      have s3 := store4' hset (w := 8) (w' := max 8 (n - 4)) (off := n - 8)
        (a := regs.x0 + (regs.x2 + 0xfffffffffffffff8)) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 8 (by omega))
      have s4 := store4' hset (w := max 8 (n - 4)) (w' := n) (off := n - 4)
        (a := regs.x0 + (regs.x2 + (0xfffffffffffffff8 + 4))) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 4 (by omega))
      rw [p0] at l1 l2 l3 l4 s1
      mc_step_ex_with step_copySmall hc 20 copySmallInsn [l1, l2, z4]
      mc_step_ex_with step_copySmall hc 21 copySmallInsn [l3, l4]
      mc_step_ex_with step_copySmall hc 22 copySmallInsn [s1, s2, z4]
      mc_step_ex_with step_copySmall hc 23 copySmallInsn [s3, s4]
      mc_step_ex step_copySmall hc 24 copySmallInsn
      mc_step_ex step_copySmall hc 25 copySmallInsn
      refine ⟨0, _, Arm64.run_zero _ _, rfl, rfl, ?_,
        ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
         hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
         hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩⟩
      simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]
  · have hb3 : ¬ (regs.x2 < 16) := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h16
    mc_step_ex_with step_copySmall hc 3 copySmallInsn [hb3]
    mc_step_ex step_copySmall hc 4 copySmallInsn
    by_cases h32 : 32 < n
    · have hb5 : (32 : UInt64) < regs.x2 := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h32
      mc_step_ex_with step_copySmall hc 5 copySmallInsn [hb5]
      have z16 : (0 : UInt64) + 16 = 16 := rfl
      have l1 := load16' hset (w := 0) (off := 0) (by omega) (by omega) a0
      have l2 := load16' hset (w := 0) (off := 16) (a := regs.x1 + 16) (by omega) (by omega)
        (by rw [hx1]; rfl)
      have l3 := load16' hset (w := 0) (off := n - 32)
        (a := regs.x1 + (regs.x2 + 0xffffffffffffffe0)) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 32 (by omega))
      have l4 := load16' hset (w := 0) (off := n - 16)
        (a := regs.x1 + (regs.x2 + (0xffffffffffffffe0 + 16))) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 16 (by omega))
      have s1 := store16' hset (w := 0) (w' := 16) (off := 0) (by omega) (by omega) (by omega) d0
      have s2 := store16' hset (w := 16) (w' := 32) (off := 16) (a := regs.x0 + 16) (by omega)
        (by omega) (by omega) (by rw [hx0]; rfl)
      have s3 := store16' hset (w := 32) (w' := max 32 (n - 16)) (off := n - 32)
        (a := regs.x0 + (regs.x2 + 0xffffffffffffffe0)) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 32 (by omega))
      have s4 := store16' hset (w := max 32 (n - 16)) (w' := n) (off := n - 16)
        (a := regs.x0 + (regs.x2 + (0xffffffffffffffe0 + 16))) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 16 (by omega))
      rw [p0] at l1 l2 l3 l4 s1
      mc_step_ex_with step_copySmall hc 12 copySmallInsn [l1, l2, z16]
      mc_step_ex_with step_copySmall hc 13 copySmallInsn [l3, l4]
      mc_step_ex_with step_copySmall hc 14 copySmallInsn [s1, s2, z16]
      mc_step_ex_with step_copySmall hc 15 copySmallInsn [s3, s4]
      mc_step_ex step_copySmall hc 16 copySmallInsn
      mc_step_ex step_copySmall hc 17 copySmallInsn
      refine ⟨0, _, Arm64.run_zero _ _, rfl, rfl, ?_,
        ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
         hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
         hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩⟩
      simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]
    · have hb5 : ¬ ((32 : UInt64) < regs.x2) := by rw [UInt64.lt_iff_toNat_lt, hx2n]; exact h32
      mc_step_ex_with step_copySmall hc 5 copySmallInsn [hb5]
      have z8 : (0 : UInt64) + 8 = 8 := rfl
      have l1 := load8' hset (w := 0) (off := 0) (by omega) (by omega) a0
      have l2 := load8' hset (w := 0) (off := 8) (a := regs.x1 + 8) (by omega) (by omega)
        (by rw [hx1]; rfl)
      have l3 := load8' hset (w := 0) (off := n - 16)
        (a := regs.x1 + (regs.x2 + 0xfffffffffffffff0)) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 16 (by omega))
      have l4 := load8' hset (w := 0) (off := n - 8)
        (a := regs.x1 + (regs.x2 + (0xfffffffffffffff0 + 8))) (by omega) (by omega)
        (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 8 (by omega))
      have s1 := store8' hset (w := 0) (w' := 8) (off := 0) (by omega) (by omega) (by omega) d0
      have s2 := store8' hset (w := 8) (w' := 16) (off := 8) (a := regs.x0 + 8) (by omega)
        (by omega) (by omega) (by rw [hx0]; rfl)
      have s3 := store8' hset (w := 16) (w' := max 16 (n - 8)) (off := n - 16)
        (a := regs.x0 + (regs.x2 + 0xfffffffffffffff0)) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 16 (by omega))
      have s4 := store8' hset (w := max 16 (n - 8)) (w' := n) (off := n - 8)
        (a := regs.x0 + (regs.x2 + (0xfffffffffffffff0 + 8))) (by omega) (by omega) (by omega)
        (by rw [hx0, hx2, ← UInt64.add_assoc]; exact copy_sub_addr dst n 8 (by omega))
      rw [p0] at l1 l2 l3 l4 s1
      mc_step_ex_with step_copySmall hc 6 copySmallInsn [l1, l2, z8]
      mc_step_ex_with step_copySmall hc 7 copySmallInsn [l3, l4]
      mc_step_ex_with step_copySmall hc 8 copySmallInsn [s1, s2, z8]
      mc_step_ex_with step_copySmall hc 9 copySmallInsn [s3, s4]
      mc_step_ex step_copySmall hc 10 copySmallInsn
      mc_step_ex step_copySmall hc 11 copySmallInsn
      refine ⟨0, _, Arm64.run_zero _ _, rfl, rfl, ?_,
        ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
         hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
         hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩⟩
      simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]

/-! ### Exported machine-code specification -/

/-- Machine-code specification of `leancrc32c_copy_small` (48 instructions).

From any state `s` at the routine's entry with `X0 = dst`, `X1 = src`,
`X2 = n` for `1 ≤ n ≤ 64`, where the `n` source bytes `b` are readable, the `n`
destination bytes are writable, and the two ranges neither wrap nor overlap
(`Setup`), execution terminates at the return address `s.regs.x30` with:
- every destination byte equal to the corresponding source byte,
- every byte outside `[dst, dst + n)` unchanged, permissions included,
- `W0` equal to the incoming `W3` (the CRC passed through to the caller), and
- `CalleeSaved s s'`: `SP`, `X19..X30` and `D8..D15` preserved (AAPCS64).

As for `copyLarge_mc_spec`, termination in the faulting model shows the routine
reads only the source range and writes only the destination range. -/
theorem copySmall_mc_spec {code : UInt64 → Option UInt32} {base : UInt64}
    {s : Arm64.ArmState} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hc : CopySmallLoaded code base) (hset : Setup s.mem src dst b n)
    (hn1 : 1 ≤ n) (hn64 : n ≤ 64)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = dst) (hx1 : s.regs.x1 = src)
    (hx2 : s.regs.x2 = n.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      (∀ i < n, s'.mem (dst + i.toUInt64) = some (.rw, b i)) ∧
      (∀ a : UInt64, ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + n) → s'.mem a = s.mem a) ∧
      s'.getW r0 = s.getW r3 ∧
      CalleeSaved s s' := by
  obtain ⟨k, s', hrun, hpc', hmem, hw0, hcs⟩ :=
    copySmall_mc_core hc hset hn1 hn64 hpc hx0 hx1 hx2
  refine ⟨k, s', hrun, hpc', ?_, ?_, hw0, hcs⟩
  · intro i hi
    have hA : (dst + i.toUInt64).toNat = dst.toNat + i :=
      Copy.toNat_add_nat _ _ (by have := hset.hd; omega)
    have hin : dst.toNat ≤ dst.toNat + i ∧ dst.toNat + i < dst.toNat + n := by omega
    rw [hmem]
    simp only [patch, hA]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    congr 3; omega
  · intro a ha
    rw [hmem]
    simp only [patch]
    rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]

end Crc32c.Arm64MC
