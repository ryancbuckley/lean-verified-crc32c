/-
Machine-code verification of `leancrc32c_copy_large` (31 instructions,
hand-written in `cxx/leancrc32c_copy_arm64.S`): copying `n ≥ 64` bytes between
non-overlapping buffers.
-/
import MemcpyCrc32c.Arm64.HwLoop
import MemcpyCrc32c.Arm64.CopyMem

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Code bytes, decoded instructions, and the fetch/decode certificate -/

def copyWords : Array UInt32 := #[
  0x8b020024, 0xad7e0c82, 0xad7f1484, 0xad400420, 0x8b020005, 0x91008003, 0x927be863, 0xcb000066,
  0x8b060021, 0xad000400, 0xd10100a7, 0xeb07007f, 0x54000202, 0xf140805f, 0x54000102, 0xad400420,
  0x91008021, 0xad000460, 0x91008063, 0xeb07007f, 0x54ffff63, 0x14000007, 0xac400420, 0x91008021,
  0xac000460, 0x91008063, 0xeb07007f, 0x54ffff63, 0xad3e0ca2, 0xad3f14a4, 0xd65f03c0]

theorem copyWords_size : copyWords.size = 31 := rfl

def copyInsn (idx : Nat) : Arm64.Instr :=
  if idx < 16 then
    if idx < 8 then
      if idx < 4 then
        if idx < 2 then
          if idx < 1 then
            .addSubReg true false false .lsl r4 r1 r2 0
          else
            .ldpQ .signedOffset r2 r3 r4 0xffffffffffffffc0
        else
          if idx < 3 then
            .ldpQ .signedOffset r4 r5 r4 0xffffffffffffffe0
          else
            .ldpQ .signedOffset r0 r1 r1 0
      else
        if idx < 6 then
          if idx < 5 then
            .addSubReg true false false .lsl r5 r0 r2 0
          else
            .addSubImm true false false r3 r0 0x20
        else
          if idx < 7 then
            .logicImm true .andOp r3 r3 0xffffffffffffffe0
          else
            .addSubReg true true false .lsl r6 r3 r0 0
    else
      if idx < 12 then
        if idx < 10 then
          if idx < 9 then
            .addSubReg true false false .lsl r1 r1 r6 0
          else
            .stpQ .signedOffset r0 r1 r0 0
        else
          if idx < 11 then
            .addSubImm true true false r7 r5 0x40
          else
            .addSubReg true true true .lsl r31 r3 r7 0
      else
        if idx < 14 then
          if idx < 13 then
            .bCond c2 0x40
          else
            .addSubImm true true true r31 r2 0x20000
        else
          if idx < 15 then
            .bCond c2 0x20
          else
            .ldpQ .signedOffset r0 r1 r1 0
  else
    if idx < 24 then
      if idx < 20 then
        if idx < 18 then
          if idx < 17 then
            .addSubImm true false false r1 r1 0x20
          else
            .stpQ .signedOffset r0 r1 r3 0
        else
          if idx < 19 then
            .addSubImm true false false r3 r3 0x20
          else
            .addSubReg true true true .lsl r31 r3 r7 0
      else
        if idx < 22 then
          if idx < 21 then
            .bCond c3 0xffffffffffffffec
          else
            .b 0x1c
        else
          if idx < 23 then
            .ldpQ .signedOffset r0 r1 r1 0
          else
            .addSubImm true false false r1 r1 0x20
    else
      if idx < 28 then
        if idx < 26 then
          if idx < 25 then
            .stpQ .signedOffset r0 r1 r3 0
          else
            .addSubImm true false false r3 r3 0x20
        else
          if idx < 27 then
            .addSubReg true true true .lsl r31 r3 r7 0
          else
            .bCond c3 0xffffffffffffffec
      else
        if idx < 30 then
          if idx < 29 then
            .stpQ .signedOffset r2 r3 r5 0xffffffffffffffc0
          else
            .stpQ .signedOffset r4 r5 r5 0xffffffffffffffe0
        else
          .ret r30

set_option maxRecDepth 8192 in
private theorem copy_decode_ok : checkWordsAux copyWords copyInsn 31 = true := rfl

/-- The 31 instruction words of `leancrc32c_copy_large` are loaded at `base`. -/
def CopyLoaded (code : UInt64 → Option UInt32) (base : UInt64) : Prop :=
  ∀ idx (h : idx < copyWords.size), code (base + (4 * idx).toUInt64) = some copyWords[idx]

theorem step_copy {code : UInt64 → Option UInt32} {base : UInt64}
    (hc : CopyLoaded code base) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = base + (4 * idx).toUInt64)
    (hok : decide (idx < 31) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (copyInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < copyWords.size := by rw [copyWords_size]; exact hp
  have hfetch := hc idx hsz
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch
    (checkWordsAux_spec copyWords copyInsn 31 copy_decode_ok idx hsz hp)

open Copy

/-! ### Address arithmetic -/

theorem copy_sub_addr (p : UInt64) (n k : Nat) (hk : k ≤ n) :
    p + n.toUInt64 + (0 - k.toUInt64) = p + (n - k).toUInt64 := by
  have e : n.toUInt64 = (n - k).toUInt64 + k.toUInt64 := by
    rw [← nat_add_toUInt64]; congr 1; omega
  have cancel : ∀ x y z : UInt64, x + (y + z) + (0 - z) = x + y := by
    intro x y z
    apply UInt64.eq_of_toBitVec_eq
    have h0 : (0 : UInt64).toBitVec = 0#64 := rfl
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, h0]
    bv_omega
  rw [e, cancel]

theorem copy_sub_addr' (p : UInt64) (n k : Nat) (hk : k ≤ n) :
    p + n.toUInt64 - k.toUInt64 = p + (n - k).toUInt64 := by
  have e : n.toUInt64 = (n - k).toUInt64 + k.toUInt64 := by
    rw [← nat_add_toUInt64]; congr 1; omega
  have cancel : ∀ x y z : UInt64, x + (y + z) - z = x + y := by
    intro x y z
    apply UInt64.eq_of_toBitVec_eq
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
    bv_omega
  rw [e, cancel]

theorem u64_add_sub_cancel_left (x y : UInt64) : x + y - x = y := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
  bv_omega

theorem store16' {m0 : Arm64.Mem} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (h : Setup m0 src dst b n) {w w' off : Nat} (how : off ≤ w) (ho : off + 16 ≤ n)
    (hw' : w' = max w (off + 16)) {a : UInt64} (ha : a = dst + off.toUInt64) :
    (patch m0 dst b w).writeV128LE a (vec b off) = some (patch m0 dst b w') := by
  rw [ha, hw']; exact Copy.store16 h how ho

theorem load16' {m0 : Arm64.Mem} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (h : Setup m0 src dst b n) {w off : Nat} (hw : w ≤ n) (ho : off + 16 ≤ n)
    {a : UInt64} (ha : a = src + off.toUInt64) :
    (patch m0 dst b w).readV128LE a = some (vec b off) := by
  rw [ha]; exact Copy.load16 h hw ho

/-! ### Tail: store the saved last 64 bytes and return (`idx = 28..30`) -/

private theorem copy_tail {code : UInt64 → Option UInt32} {base : UInt64}
    (hc : CopyLoaded code base) {s0 s : Arm64.ArmState} {m0 : Arm64.Mem}
    {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hset : Setup m0 src dst b n) (hn : 64 ≤ n) {w : Nat} (hw1 : n - 64 ≤ w) (hw2 : w ≤ n)
    (hpc : s.pc = base + 112)
    (hx5 : s.regs.x5 = dst + n.toUInt64)
    (hx30 : s.regs.x30 = s0.regs.x30)
    (hv2 : s.simd.v2 = vec b (n - 64)) (hv3 : s.simd.v3 = vec b (n - 48))
    (hv4 : s.simd.v4 = vec b (n - 32)) (hv5 : s.simd.v5 = vec b (n - 16))
    (hmem : s.mem = patch m0 dst b w)
    (hcs : CalleeSaved s0 s) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s0.regs.x30 ∧ s'.mem = patch m0 dst b n ∧ CalleeSaved s0 s' := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hpc hx5 hx30 hv2 hv3 hv4 hv5 hmem
  subst hpc hmem
  have a1 : regs.x5 + 0xffffffffffffffc0 = dst + (n - 64).toUInt64 := by
    rw [hx5]; exact copy_sub_addr dst n 64 hn
  have a2 : regs.x5 + (0xffffffffffffffc0 + 16) = dst + (n - 48).toUInt64 := by
    rw [hx5]; exact copy_sub_addr dst n 48 (by omega)
  have a3 : regs.x5 + 0xffffffffffffffe0 = dst + (n - 32).toUInt64 := by
    rw [hx5]; exact copy_sub_addr dst n 32 (by omega)
  have a4 : regs.x5 + (0xffffffffffffffe0 + 16) = dst + (n - 16).toUInt64 := by
    rw [hx5]; exact copy_sub_addr dst n 16 (by omega)
  have st1 := store16' hset (w := w) (w' := max w (n - 48)) (off := n - 64) hw1 (by omega)
    (by congr 1; omega) a1
  have st2 := store16' hset (w := max w (n - 48)) (w' := max w (n - 32)) (off := n - 48)
    (by omega) (by omega) (by omega) a2
  have st3 := store16' hset (w := max w (n - 32)) (w' := max w (n - 16)) (off := n - 32)
    (by omega) (by omega) (by omega) a3
  have st4 := store16' hset (w := max w (n - 16)) (w' := n) (off := n - 16)
    (by omega) (by omega) (by omega) a4
  rw [← hv2] at st1; rw [← hv3] at st2; rw [← hv4] at st3; rw [← hv5] at st4
  mc_step_ex_with step_copy hc 28 copyInsn [st1, st2]
  mc_step_ex_with step_copy hc 29 copyInsn [st3, st4]
  mc_step_ex step_copy hc 30 copyInsn
  refine ⟨0, _, Arm64.run_zero _ _, hx30, rfl, ?_⟩
  exact ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
    hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
    hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩

/-! ### Block loop A (`idx = 15..20`): 32 bytes per iteration -/

private theorem copy_loopA {code : UInt64 → Option UInt32} {base : UInt64}
    (hc : CopyLoaded code base) {s0 : Arm64.ArmState} {m0 : Arm64.Mem}
    {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hset : Setup m0 src dst b n) (hn : 64 ≤ n) :
    ∀ (rem : Nat) (s : Arm64.ArmState) (k w : Nat),
      s.pc = base + 60 →
      s.regs.x1 = src + k.toUInt64 →
      s.regs.x3 = dst + k.toUInt64 →
      s.regs.x7 = dst + (n - 64).toUInt64 →
      s.regs.x5 = dst + n.toUInt64 →
      s.regs.x30 = s0.regs.x30 →
      s.simd.v2 = vec b (n - 64) → s.simd.v3 = vec b (n - 48) →
      s.simd.v4 = vec b (n - 32) → s.simd.v5 = vec b (n - 16) →
      s.mem = patch m0 dst b w →
      k ≤ w → w ≤ n → k < n - 64 → n - 64 - k = rem →
      CalleeSaved s0 s →
      ∃ j s', Arm64.run code j s = some s' ∧
        s'.pc = s0.regs.x30 ∧ s'.mem = patch m0 dst b n ∧ CalleeSaved s0 s' := by
  have hd := hset.hd
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s k w hpc hx1 hx3 hx7 hx5 hx30 hv2 hv3 hv4 hv5 hmem hkw hwn hk hrem hcs
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hpc hx1 hx3 hx7 hx5 hx30 hv2 hv3 hv4 hv5 hmem
    subst hpc hmem
    have e16 (q : UInt64) : q + k.toUInt64 + 16 = q + (k + 16).toUInt64 := by
      rw [nat_add_toUInt64, UInt64.add_assoc]; rfl
    have e32 (q : UInt64) : q + k.toUInt64 + 32 = q + (k + 32).toUInt64 := by
      rw [nat_add_toUInt64, UInt64.add_assoc]; rfl
    have ld1 := load16' hset (w := w) (off := k) hwn (by omega) hx1
    have ld2 := load16' hset (w := w) (off := k + 16) (a := regs.x1 + 16) hwn (by omega)
      (by rw [hx1, e16])
    have st1 := store16' hset (w := w) (w' := max w (k + 16)) (off := k) hkw (by omega) rfl hx3
    have st2 := store16' hset (w := max w (k + 16)) (w' := max w (k + 32)) (off := k + 16)
      (a := regs.x3 + 16) (by omega) (by omega) (by omega) (by rw [hx3, e16])
    have z16 : (0 : UInt64) + 16 = 16 := rfl
    mc_step_ex_with step_copy hc 15 copyInsn [ld1, ld2, z16]
    mc_step_ex step_copy hc 16 copyInsn
    mc_step_ex_with step_copy hc 17 copyInsn [st1, st2, z16]
    mc_step_ex step_copy hc 18 copyInsn
    mc_step_ex step_copy hc 19 copyInsn
    have hx3n : (regs.x3 + 32).toNat = dst.toNat + (k + 32) := by
      rw [hx3, e32]; exact Copy.toNat_add_nat _ _ (by omega)
    have hx7n : regs.x7.toNat = dst.toNat + (n - 64) := by
      rw [hx7]; exact Copy.toNat_add_nat _ _ (by omega)
    by_cases hmore : k + 32 < n - 64
    · have hb : regs.x3 + 32 < regs.x7 := by
        rw [UInt64.lt_iff_toNat_lt, hx3n, hx7n]; omega
      mc_step_ex_with step_copy hc 20 copyInsn [hb]
      refine ih (n - 64 - (k + 32)) (by omega) _ (k + 32) (max w (k + 32)) ?_ ?_ ?_ hx7 hx5 hx30
        hv2 hv3 hv4 hv5 rfl (by omega) (by omega) hmore rfl
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
      · rfl
      · dsimp only; rw [hx1, e32]
      · dsimp only; rw [hx3, e32]
    · have hb : ¬ (regs.x3 + 32 < regs.x7) := by
        rw [UInt64.lt_iff_toNat_lt, hx3n, hx7n]; omega
      mc_step_ex_with step_copy hc 20 copyInsn [hb]
      mc_step_ex step_copy hc 21 copyInsn
      exact copy_tail hc hset hn (w := max w (k + 32)) (by omega) (by omega) rfl hx5 hx30
        hv2 hv3 hv4 hv5 rfl
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩

/-! ### Block loop B (`idx = 22..27`): 32 bytes per iteration -/

private theorem copy_loopB {code : UInt64 → Option UInt32} {base : UInt64}
    (hc : CopyLoaded code base) {s0 : Arm64.ArmState} {m0 : Arm64.Mem}
    {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hset : Setup m0 src dst b n) (hn : 64 ≤ n) :
    ∀ (rem : Nat) (s : Arm64.ArmState) (k w : Nat),
      s.pc = base + 88 →
      s.regs.x1 = src + k.toUInt64 →
      s.regs.x3 = dst + k.toUInt64 →
      s.regs.x7 = dst + (n - 64).toUInt64 →
      s.regs.x5 = dst + n.toUInt64 →
      s.regs.x30 = s0.regs.x30 →
      s.simd.v2 = vec b (n - 64) → s.simd.v3 = vec b (n - 48) →
      s.simd.v4 = vec b (n - 32) → s.simd.v5 = vec b (n - 16) →
      s.mem = patch m0 dst b w →
      k ≤ w → w ≤ n → k < n - 64 → n - 64 - k = rem →
      CalleeSaved s0 s →
      ∃ j s', Arm64.run code j s = some s' ∧
        s'.pc = s0.regs.x30 ∧ s'.mem = patch m0 dst b n ∧ CalleeSaved s0 s' := by
  have hd := hset.hd
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s k w hpc hx1 hx3 hx7 hx5 hx30 hv2 hv3 hv4 hv5 hmem hkw hwn hk hrem hcs
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hpc hx1 hx3 hx7 hx5 hx30 hv2 hv3 hv4 hv5 hmem
    subst hpc hmem
    have e16 (q : UInt64) : q + k.toUInt64 + 16 = q + (k + 16).toUInt64 := by
      rw [nat_add_toUInt64, UInt64.add_assoc]; rfl
    have e32 (q : UInt64) : q + k.toUInt64 + 32 = q + (k + 32).toUInt64 := by
      rw [nat_add_toUInt64, UInt64.add_assoc]; rfl
    have ld1 := load16' hset (w := w) (off := k) hwn (by omega) hx1
    have ld2 := load16' hset (w := w) (off := k + 16) (a := regs.x1 + 16) hwn (by omega)
      (by rw [hx1, e16])
    have st1 := store16' hset (w := w) (w' := max w (k + 16)) (off := k) hkw (by omega) rfl hx3
    have st2 := store16' hset (w := max w (k + 16)) (w' := max w (k + 32)) (off := k + 16)
      (a := regs.x3 + 16) (by omega) (by omega) (by omega) (by rw [hx3, e16])
    have z16 : (0 : UInt64) + 16 = 16 := rfl
    mc_step_ex_with step_copy hc 22 copyInsn [ld1, ld2, z16]
    mc_step_ex step_copy hc 23 copyInsn
    mc_step_ex_with step_copy hc 24 copyInsn [st1, st2, z16]
    mc_step_ex step_copy hc 25 copyInsn
    mc_step_ex step_copy hc 26 copyInsn
    have hx3n : (regs.x3 + 32).toNat = dst.toNat + (k + 32) := by
      rw [hx3, e32]; exact Copy.toNat_add_nat _ _ (by omega)
    have hx7n : regs.x7.toNat = dst.toNat + (n - 64) := by
      rw [hx7]; exact Copy.toNat_add_nat _ _ (by omega)
    by_cases hmore : k + 32 < n - 64
    · have hb : regs.x3 + 32 < regs.x7 := by
        rw [UInt64.lt_iff_toNat_lt, hx3n, hx7n]; omega
      mc_step_ex_with step_copy hc 27 copyInsn [hb]
      refine ih (n - 64 - (k + 32)) (by omega) _ (k + 32) (max w (k + 32)) ?_ ?_ ?_ hx7 hx5 hx30
        hv2 hv3 hv4 hv5 rfl (by omega) (by omega) hmore rfl
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩
      · rfl
      · dsimp only; rw [hx1, e32]
      · dsimp only; rw [hx3, e32]
    · have hb : ¬ (regs.x3 + 32 < regs.x7) := by
        rw [UInt64.lt_iff_toNat_lt, hx3n, hx7n]; omega
      mc_step_ex_with step_copy hc 27 copyInsn [hb]
      exact copy_tail hc hset hn (w := max w (k + 32)) (by omega) (by omega) rfl hx5 hx30
        hv2 hv3 hv4 hv5 rfl
        ⟨hcs.sp, hcs.x19, hcs.x20, hcs.x21, hcs.x22, hcs.x23, hcs.x24,
         hcs.x25, hcs.x26, hcs.x27, hcs.x28, hcs.x29, hcs.x30,
         hcs.d8, hcs.d9, hcs.d10, hcs.d11, hcs.d12, hcs.d13, hcs.d14, hcs.d15⟩

/-! ### Destination alignment -/

set_option linter.unusedSimpArgs false in
theorem and_mask32 (x : UInt64) :
    (x &&& (0xffffffffffffffe0 : UInt64)).toNat = x.toNat / 32 * 32 := by
  have e : x &&& (0xffffffffffffffe0 : UInt64) = (x >>> 5) <<< 5 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hm : (0xffffffffffffffe0 : UInt64).toBitVec = 0xffffffffffffffe0#64 := rfl
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hm,
      BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    interval_cases i <;> simp
  rw [e]
  have := x.toNat_lt
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The first 32-byte-aligned address strictly above `d` is `d + k0` with `1 ≤ k0 ≤ 32`. -/
theorem align32 (d : UInt64) (hd : d.toNat + 32 < 2 ^ 64) :
    ∃ k0, 1 ≤ k0 ∧ k0 ≤ 32 ∧ (d + 32) &&& (0xffffffffffffffe0 : UInt64) = d + k0.toUInt64 := by
  refine ⟨32 - d.toNat % 32, by omega, by omega, Copy.u64_ext ?_⟩
  have h32 : (d + 32).toNat = d.toNat + 32 := Copy.toNat_add_nat d 32 (by omega)
  rw [and_mask32, h32, Copy.toNat_add_nat _ _ (by omega)]
  omega

/-! ### Entry: head, alignment, and dispatch to a block loop or straight to the tail -/

theorem copyLarge_mc_core {code : UInt64 → Option UInt32} {base : UInt64}
    {s : Arm64.ArmState} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hc : CopyLoaded code base) (hset : Setup s.mem src dst b n) (hn : 64 ≤ n)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = dst) (hx1 : s.regs.x1 = src)
    (hx2 : s.regs.x2 = n.toUInt64) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = s.regs.x30 ∧ s'.mem = patch s.mem dst b n ∧ CalleeSaved s s' := by
  have hd := hset.hd
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hset hpc hx0 hx1 hx2 ⊢
  subst hpc
  have p0 := patch_zero mem dst b
  have z16 : (0 : UInt64) + 16 = 16 := rfl
  have ldT1 := load16' hset (w := 0) (off := n - 64)
    (a := regs.x1 + (regs.x2 + 0xffffffffffffffc0)) (by omega) (by omega)
    (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 64 hn)
  have ldT2 := load16' hset (w := 0) (off := n - 48)
    (a := regs.x1 + (regs.x2 + (0xffffffffffffffc0 + 16))) (by omega) (by omega)
    (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 48 (by omega))
  have ldT3 := load16' hset (w := 0) (off := n - 32)
    (a := regs.x1 + (regs.x2 + 0xffffffffffffffe0)) (by omega) (by omega)
    (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 32 (by omega))
  have ldT4 := load16' hset (w := 0) (off := n - 16)
    (a := regs.x1 + (regs.x2 + (0xffffffffffffffe0 + 16))) (by omega) (by omega)
    (by rw [hx1, hx2, ← UInt64.add_assoc]; exact copy_sub_addr src n 16 (by omega))
  have ldH1 := load16' hset (w := 0) (off := 0) (a := regs.x1) (by omega) (by omega)
    (by rw [hx1]; simp [Nat.toUInt64])
  have ldH2 := load16' hset (w := 0) (off := 16) (a := regs.x1 + 16) (by omega) (by omega)
    (by rw [hx1]; rfl)
  have st1 := store16' hset (w := 0) (w' := 16) (off := 0) (a := regs.x0) (by omega) (by omega)
    (by omega) (by rw [hx0]; simp [Nat.toUInt64])
  have st2 := store16' hset (w := 16) (w' := 32) (off := 16) (a := regs.x0 + 16) (by omega)
    (by omega) (by omega) (by rw [hx0]; rfl)
  rw [p0] at ldT1 ldT2 ldT3 ldT4 ldH1 ldH2 st1
  mc_step_ex step_copy hc 0 copyInsn
  mc_step_ex_with step_copy hc 1 copyInsn [ldT1, ldT2]
  mc_step_ex_with step_copy hc 2 copyInsn [ldT3, ldT4]
  mc_step_ex_with step_copy hc 3 copyInsn [ldH1, ldH2, z16]
  mc_step_ex step_copy hc 4 copyInsn
  mc_step_ex step_copy hc 5 copyInsn
  mc_step_ex step_copy hc 6 copyInsn
  mc_step_ex step_copy hc 7 copyInsn
  mc_step_ex step_copy hc 8 copyInsn
  mc_step_ex_with step_copy hc 9 copyInsn [st1, st2, z16]
  mc_step_ex step_copy hc 10 copyInsn
  mc_step_ex step_copy hc 11 copyInsn
  -- name the register values the rest of the routine uses
  obtain ⟨k0, hk1, hk2, hal⟩ := align32 regs.x0 (by rw [hx0]; omega)
  have hx3 : regs.x0 + 32 &&& (0xffffffffffffffe0 : UInt64) = dst + k0.toUInt64 := by
    rw [hal, hx0]
  have hx1' : regs.x1 + ((regs.x0 + 32 &&& (0xffffffffffffffe0 : UInt64)) - regs.x0) =
      src + k0.toUInt64 := by
    rw [hal, hx1, u64_add_sub_cancel_left]
  have hx5 : regs.x0 + regs.x2 = dst + n.toUInt64 := by rw [hx0, hx2]
  have hx7 : regs.x0 + regs.x2 - 64 = dst + (n - 64).toUInt64 := by
    rw [hx0, hx2]; exact copy_sub_addr' dst n 64 hn
  have hx3n : (regs.x0 + 32 &&& (0xffffffffffffffe0 : UInt64)).toNat = dst.toNat + k0 := by
    rw [hx3]; exact Copy.toNat_add_nat _ _ (by omega)
  have hx7n : (regs.x0 + regs.x2 - 64).toNat = dst.toNat + (n - 64) := by
    rw [hx7]; exact Copy.toNat_add_nat _ _ (by omega)
  have hcs0 : CalleeSaved
      ({ regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem } : Arm64.ArmState)
      ({ regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem } : Arm64.ArmState) :=
    CalleeSaved.refl _
  by_cases hgo : k0 < n - 64
  · have hb12 : ¬ (regs.x0 + regs.x2 - 64 ≤ regs.x0 + 32 &&& (0xffffffffffffffe0 : UInt64)) := by
      rw [UInt64.le_iff_toNat_le, hx3n, hx7n]; omega
    mc_step_ex_with step_copy hc 12 copyInsn [hb12]
    mc_step_ex step_copy hc 13 copyInsn
    have hlt : n < 2 ^ 64 := by
      have := hset.disj; have := src.toNat_lt; have := dst.toNat_lt; omega
    have hx2n : regs.x2.toNat = n := by rw [hx2]; exact nat_toUInt64_toNat n hlt
    by_cases hbig : 131072 ≤ n
    · have hb14 : (131072 : UInt64) ≤ regs.x2 := by
        rw [UInt64.le_iff_toNat_le, hx2n]; exact hbig
      mc_step_ex_with step_copy hc 14 copyInsn [hb14]
      refine copy_loopB hc (s0 := { regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem })
        hset hn (n - 64 - k0) _ k0 32 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (by omega) (by omega) hgo rfl ?_
      all_goals first | exact hx1' | exact hx3 | exact hx7 | exact hx5 | rfl | exact
        ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
         hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
         hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩
    · have hb14 : ¬ ((131072 : UInt64) ≤ regs.x2) := by
        rw [UInt64.le_iff_toNat_le, hx2n]; exact hbig
      mc_step_ex_with step_copy hc 14 copyInsn [hb14]
      refine copy_loopA hc (s0 := { regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem })
        hset hn (n - 64 - k0) _ k0 32 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (by omega) (by omega) hgo rfl ?_
      all_goals first | exact hx1' | exact hx3 | exact hx7 | exact hx5 | rfl | exact
        ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
         hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
         hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩
  · have hb12 : regs.x0 + regs.x2 - 64 ≤ regs.x0 + 32 &&& (0xffffffffffffffe0 : UInt64) := by
      rw [UInt64.le_iff_toNat_le, hx3n, hx7n]; omega
    mc_step_ex_with step_copy hc 12 copyInsn [hb12]
    refine copy_tail hc (s0 := { regs := regs, sp := sp, simd := simd, nzcv := nzcv, pc := pc, mem := mem })
      hset hn (w := 32) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | exact hx5 | rfl | exact
      ⟨hcs0.sp, hcs0.x19, hcs0.x20, hcs0.x21, hcs0.x22, hcs0.x23, hcs0.x24,
       hcs0.x25, hcs0.x26, hcs0.x27, hcs0.x28, hcs0.x29, hcs0.x30,
       hcs0.d8, hcs0.d9, hcs0.d10, hcs0.d11, hcs0.d12, hcs0.d13, hcs0.d14, hcs0.d15⟩

/-! ### Exported machine-code specification -/

/-- Machine-code specification of `leancrc32c_copy_large` (31 instructions).

From any state `s` at the routine's entry with `X0 = dst`, `X1 = src`,
`X2 = n ≥ 64`, where the `n` source bytes `b` are readable, the `n` destination
bytes are writable, and the two ranges neither wrap nor overlap (`Setup`),
execution terminates at the return address `s.regs.x30` with:
- every destination byte equal to the corresponding source byte,
- every byte outside `[dst, dst + n)` unchanged, permissions included, and
- `CalleeSaved s s'`: `SP`, `X19..X30` and `D8..D15` preserved (AAPCS64).

Since the model's `step` fails on any read of an unmapped byte or write to a
non-`.rw` byte, termination also shows the routine reads only the source range
and writes only the destination range. It holds for both block loops, so for
the non-temporal `ldnp`/`stnp` path too. -/
theorem copyLarge_mc_spec {code : UInt64 → Option UInt32} {base : UInt64}
    {s : Arm64.ArmState} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}
    (hc : CopyLoaded code base) (hset : Setup s.mem src dst b n) (hn : 64 ≤ n)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = dst) (hx1 : s.regs.x1 = src)
    (hx2 : s.regs.x2 = n.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      (∀ i < n, s'.mem (dst + i.toUInt64) = some (.rw, b i)) ∧
      (∀ a : UInt64, ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + n) → s'.mem a = s.mem a) ∧
      CalleeSaved s s' := by
  obtain ⟨k, s', hrun, hpc', hmem, hcs⟩ := copyLarge_mc_core hc hset hn hpc hx0 hx1 hx2
  refine ⟨k, s', hrun, hpc', ?_, ?_, hcs⟩
  · intro i hi
    have hA : (dst + i.toUInt64).toNat = dst.toNat + i :=
      Copy.toNat_add_nat _ _ (by have := hset.hd; omega)
    rw [hmem]
    simp only [patch, hA]
    have hin : dst.toNat ≤ dst.toNat + i ∧ dst.toNat + i < dst.toNat + n := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    congr 3; omega
  · intro a ha
    rw [hmem]
    simp only [patch]
    rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]

end Crc32c.Arm64MC
