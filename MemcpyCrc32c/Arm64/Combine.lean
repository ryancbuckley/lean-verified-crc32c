/-
Machine-code verification of `_lp_leancrc32c_Crc32c_combine3` (`44` instructions)
and `_lp_leancrc32c_Crc32c_combine6` (`65` instructions) from `HwCombine.c.o`
against `Crc32c.combine3` and `Crc32c.combine6`.

Proves termination, functional equivalence across both the `< 512`-word 2 KiB
lookup-table fast path and the `≥ 512`-word `hwPowGo` square-and-multiply loop,
zero stack usage (`s'.mem = s.mem`, `s'.sp = s.sp`), and full AAPCS64 register
preservation (`CalleeSaved s s'`). Kernel-checked without `bv_decide`.
-/
import MemcpyCrc32c.Arm64.Step

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Arithmetic & table-lookup helpers for `hwShiftWords` and `hwPowGo` -/

private theorem u32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem csel_odd_bit (n : UInt64) (acc mul : UInt32) :
    (if (n.toUInt32 &&& (0x1 : UInt64).toUInt32) == 0 then acc else mul) =
      (if n &&& 1 = 1 then mul else acc) := by
  change (if (n.toUInt32 &&& 1) == 0 then acc else mul) = (if n &&& 1 = 1 then mul else acc)
  have e32 : (n.toUInt32 &&& 1).toNat = n.toNat % 2 := by
    rw [UInt32.toNat_and]
    change (n.toNat % 2 ^ 32) &&& 1 = n.toNat % 2
    rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]
  have e64 : (n &&& 1).toNat = n.toNat % 2 := by
    rw [UInt64.toNat_and]
    exact Nat.and_one_is_mod n.toNat
  by_cases hmod : n.toNat % 2 = 0
  · have hz : n.toUInt32 &&& 1 = 0 := u32_ext (by rw [e32, hmod]; rfl)
    have hne : n &&& 1 ≠ 1 := fun h1 => by
      have hto : (n &&& 1).toNat = 1 := congrArg UInt64.toNat h1
      omega
    rw [hz]
    simp [hne]
  · have hmod1 : n.toNat % 2 = 1 := by omega
    have hnz : n.toUInt32 &&& 1 ≠ 0 := fun h0 => by
      have hto : (n.toUInt32 &&& 1).toNat = 0 := congrArg UInt32.toNat h0
      omega
    have heq1 : n &&& 1 = 1 := u64_ext (by rw [e64, hmod1]; rfl)
    simp [hnz, heq1]

private theorem hwPowGo_step_eq (b acc : UInt32) (n : UInt64) (hn : 1 ≤ n.toNat) :
    Crc32c.hwPowGo b acc n =
      if 2 ≤ n.toNat then
        Crc32c.hwPowGo (Crc32c.hwMul b b) (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc) (n >>> 1)
      else
        (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc) := by
  have hne0 : n ≠ 0 := fun h0 => by subst h0; simp at hn
  conv_lhs => rw [Crc32c.hwPowGo]
  simp only [hne0, ↓reduceDIte]
  by_cases h2 : 2 ≤ n.toNat
  · simp [h2]
  · have h1 : n.toNat = 1 := by omega
    have hsh : n >>> 1 = 0 := u64_ext (by rw [UInt64.toNat_shiftRight, h1]; rfl)
    simp only [h2, ↓reduceIte, hsh]
    rw [Crc32c.hwPowGo]
    simp

private theorem hwMul_fold (a b : UInt32) :
    SimdModels.crc32c_u64 0 (SimdModels.clmulLo a.toUInt64 b.toUInt64) = Crc32c.hwMul a b := rfl

private theorem tblBytes_read_hwShiftSmall {m : Arm64.Mem} {L : CodeLayout}
    (hg : GlobalsLoaded m L) (ws : USize) (hws : ws.toNat < 512) :
    m.readU32LE (L.tblObjAddr + ((ws.toUInt64 <<< (2 : Nat).toUInt64) + 0x18)) =
      some (Crc32c.hwShiftSmall ws hws) := by
  have hsh : ws.toUInt64 <<< (2 : Nat).toUInt64 = (ws.toNat * 4).toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64]
    have h2 : ((2 : Nat).toUInt64).toNat % 64 = 2 := rfl
    rw [h2, Nat.shiftLeft_eq]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', show 2 ^ 2 = 4 from rfl]
  have haddr : L.tblObjAddr + ((ws.toUInt64 <<< (2 : Nat).toUInt64) + 0x18) =
      (L.tblObjAddr + 0x18) + (ws.toNat * 4).toUInt64 := by
    rw [hsh, UInt64.add_comm ((ws.toNat * 4).toUInt64) 0x18, ← UInt64.add_assoc]
  rw [haddr]
  have hread := Arm64.Mem.hasROBytes_readU32LE hg.tblBytes (ws.toNat * 4)
    (by rw [Crc32c.hwShiftSmallBytes_size]; omega)
  rw [hread]
  apply congrArg some
  have hs : 2048 < USize.size := by have := Crc32c.usize_size_gt; omega
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have h4 : (4 : USize).toNat = 4 := by simp
  have hbase : (ws * 4).toNat = ws.toNat * 4 := by
    rw [USize.toNat_mul, h4]; exact Nat.mod_eq_of_lt (by omega)
  have r1 : (ws * 4 + 1).toNat = ws.toNat * 4 + 1 :=
    (Crc32c.usize_add_toNat (ws * 4) 1 (by omega)).trans (by omega)
  have r2 : (ws * 4 + 2).toNat = ws.toNat * 4 + 2 :=
    (Crc32c.usize_add_toNat (ws * 4) 2 (by omega)).trans (by omega)
  have r3 : (ws * 4 + 3).toNat = ws.toNat * 4 + 3 :=
    (Crc32c.usize_add_toNat (ws * 4) 3 (by omega)).trans (by omega)
  unfold Crc32c.hwShiftSmall Crc32c.load32 Crc32c.word32
  dsimp only
  simp only [Crc32c.loadU8_eq_uget,
    Crc32c.uget_eq Crc32c.hwShiftSmallBytes (ws * 4) (ws.toNat * 4) hbase,
    Crc32c.uget_eq Crc32c.hwShiftSmallBytes (ws * 4 + 1) (ws.toNat * 4 + 1) r1,
    Crc32c.uget_eq Crc32c.hwShiftSmallBytes (ws * 4 + 2) (ws.toNat * 4 + 2) r2,
    Crc32c.uget_eq Crc32c.hwShiftSmallBytes (ws * 4 + 3) (ws.toNat * 4 + 3) r3]

/-! ### `hwPowGo` loop verification (`idx = 8..23` in `combine3` and `combine6`) -/

private theorem combine3_pow_loop {code : UInt64 → Option UInt32} {L : CodeLayout} :
    ∀ (k : Nat) (s : Arm64.ArmState) (n : UInt64) (b acc : UInt32),
      CodeLoaded code s.mem L →
      s.pc = L.combine3Base + 32 →
      s.regs.x0 = n →
      s.getW r9 = b →
      s.getW r8 = acc →
      n.toNat = k →
      1 ≤ k →
      ∃ steps s', Arm64.run code steps s = some s' ∧
        s'.pc = L.combine3Base + 96 ∧
        s'.getW r8 = Crc32c.hwPowGo b acc n ∧
        s'.regs.x1 = s.regs.x1 ∧ s'.regs.x2 = s.regs.x2 ∧ s'.regs.x3 = s.regs.x3 ∧
        s'.mem = s.mem ∧ CalleeSaved s s' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s n b acc hc hpc hx0 hb hacc hk hk1
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hc hpc hx0 hb hacc
    subst hpc
    have hstep16 : ∃ s1, Arm64.run code 16 { regs, sp, simd, nzcv, pc := L.combine3Base + 32, mem } = some s1 ∧
        s1.pc = (if (2 : UInt64) ≤ n then L.combine3Base + 32 else L.combine3Base + 96) ∧
        s1.regs.x0 = n >>> 1 ∧
        s1.getW r9 = Crc32c.hwMul b b ∧
        s1.getW r8 = (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc) ∧
        s1.regs.x1 = regs.x1 ∧ s1.regs.x2 = regs.x2 ∧ s1.regs.x3 = regs.x3 ∧
        s1.mem = mem ∧ CalleeSaved { regs, sp, simd, nzcv, pc := L.combine3Base + 32, mem } s1 := by
      apply Exists.intro
      apply And.intro
      · mc_step step_combine3 hc 8 combine3Insn
        mc_step step_combine3 hc 9 combine3Insn
        mc_step step_combine3 hc 10 combine3Insn
        mc_step step_combine3 hc 11 combine3Insn
        mc_step step_combine3 hc 12 combine3Insn
        mc_step step_combine3 hc 13 combine3Insn
        mc_step step_combine3 hc 14 combine3Insn
        mc_step step_combine3 hc 15 combine3Insn
        mc_step step_combine3 hc 16 combine3Insn
        mc_step step_combine3 hc 17 combine3Insn
        mc_step step_combine3 hc 18 combine3Insn
        mc_step step_combine3 hc 19 combine3Insn
        mc_step step_combine3 hc 20 combine3Insn
        mc_step step_combine3 hc 21 combine3Insn
        mc_step step_combine3 hc 22 combine3Insn
        mc_step step_combine3 hc 23 combine3Insn
        exact Arm64.run_zero _ _
      · simp only [Arm64.ArmState.getW, Arm64.RegFile.get] at hb hacc ⊢
        rw [hx0, hb, hacc]
        refine ⟨?_, rfl, ?_, ?_, trivial, trivial, trivial, trivial,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
           rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · by_cases h2 : (2 : UInt64) ≤ n <;> simp only [h2, ↓reduceIte] <;> rfl
        · simp [Crc32c.hwMul]
        · rw [toUInt32_toUInt64, csel_odd_bit]
          by_cases h1 : n &&& 1 = 1 <;> simp [h1, Crc32c.hwMul]
    rcases hstep16 with ⟨s1, hrun1, hpc1, hx01, hb1, hacc1, hx1, hx2, hx3, hmem1, hcs1⟩
    rw [hwPowGo_step_eq b acc n (by omega)]
    by_cases h2 : 2 ≤ n.toNat
    · have h2u : (2 : UInt64) ≤ n := h2
      simp only [h2u, ↓reduceIte] at hpc1
      simp only [h2, ↓reduceIte]
      have hsh : (n >>> 1).toNat = k / 2 := by rw [UInt64.toNat_shiftRight, hk]; rfl
      have hrec := ih (k / 2) (by omega) s1 (n >>> 1) (Crc32c.hwMul b b)
        (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc)
        (hmem1 ▸ hc) hpc1 hx01 hb1 hacc1 hsh (by omega)
      refine run_bind_exists hrun1 ?_
      rcases hrec with ⟨steps2, s2, hrun2, hpc2, hr8, hx1', hx2', hx3', hmem2, hcs2⟩
      exact ⟨steps2, s2, hrun2, hpc2, hr8,
        hx1'.trans hx1, hx2'.trans hx2, hx3'.trans hx3,
        hmem2.trans hmem1, hcs1.trans hcs2⟩
    · have h2u : ¬ (2 : UInt64) ≤ n := h2
      simp only [h2u, ↓reduceIte] at hpc1
      simp only [h2, ↓reduceIte]
      exact ⟨16, s1, hrun1, hpc1, hacc1, hx1, hx2, hx3, hmem1, hcs1⟩

private theorem combine3_pow_loop_cps {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {n : UInt64} {b acc : UInt32} {P : Arm64.ArmState → Prop}
    (hc : CodeLoaded code s.mem L)
    (hpc : s.pc = L.combine3Base + 32)
    (hx0 : s.regs.x0 = n)
    (hb : s.getW r9 = b)
    (hacc : s.getW r8 = acc)
    (hn : 1 ≤ n.toNat)
    (hcont : ∀ s', s'.pc = L.combine3Base + 96 →
      s'.getW r8 = Crc32c.hwPowGo b acc n →
      s'.regs.x1 = s.regs.x1 → s'.regs.x2 = s.regs.x2 → s'.regs.x3 = s.regs.x3 →
      s'.mem = s.mem → CalleeSaved s s' →
      ∃ k s2, Arm64.run code k s' = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  rcases combine3_pow_loop n.toNat s n b acc hc hpc hx0 hb hacc rfl hn with
    ⟨k1, s', hr1, hpc', hr8', hx1', hx2', hx3', hmem', hcs'⟩
  exact run_bind_exists hr1 (hcont s' hpc' hr8' hx1' hx2' hx3' hmem' hcs')

private theorem combine6_pow_loop {code : UInt64 → Option UInt32} {L : CodeLayout} :
    ∀ (k : Nat) (s : Arm64.ArmState) (n : UInt64) (b acc : UInt32),
      CodeLoaded code s.mem L →
      s.pc = L.combine6Base + 32 →
      s.regs.x0 = n →
      s.getW r9 = b →
      s.getW r8 = acc →
      n.toNat = k →
      1 ≤ k →
      ∃ steps s', Arm64.run code steps s = some s' ∧
        s'.pc = L.combine6Base + 96 ∧
        s'.getW r8 = Crc32c.hwPowGo b acc n ∧
        s'.regs.x1 = s.regs.x1 ∧ s'.regs.x2 = s.regs.x2 ∧ s'.regs.x3 = s.regs.x3 ∧
        s'.regs.x4 = s.regs.x4 ∧ s'.regs.x5 = s.regs.x5 ∧ s'.regs.x6 = s.regs.x6 ∧
        s'.mem = s.mem ∧ CalleeSaved s s' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s n b acc hc hpc hx0 hb hacc hk hk1
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hc hpc hx0 hb hacc
    subst hpc
    have hstep16 : ∃ s1, Arm64.run code 16 { regs, sp, simd, nzcv, pc := L.combine6Base + 32, mem } = some s1 ∧
        s1.pc = (if (2 : UInt64) ≤ n then L.combine6Base + 32 else L.combine6Base + 96) ∧
        s1.regs.x0 = n >>> 1 ∧
        s1.getW r9 = Crc32c.hwMul b b ∧
        s1.getW r8 = (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc) ∧
        s1.regs.x1 = regs.x1 ∧ s1.regs.x2 = regs.x2 ∧ s1.regs.x3 = regs.x3 ∧
        s1.regs.x4 = regs.x4 ∧ s1.regs.x5 = regs.x5 ∧ s1.regs.x6 = regs.x6 ∧
        s1.mem = mem ∧ CalleeSaved { regs, sp, simd, nzcv, pc := L.combine6Base + 32, mem } s1 := by
      apply Exists.intro
      apply And.intro
      · mc_step step_combine6 hc 8 combine6Insn
        mc_step step_combine6 hc 9 combine6Insn
        mc_step step_combine6 hc 10 combine6Insn
        mc_step step_combine6 hc 11 combine6Insn
        mc_step step_combine6 hc 12 combine6Insn
        mc_step step_combine6 hc 13 combine6Insn
        mc_step step_combine6 hc 14 combine6Insn
        mc_step step_combine6 hc 15 combine6Insn
        mc_step step_combine6 hc 16 combine6Insn
        mc_step step_combine6 hc 17 combine6Insn
        mc_step step_combine6 hc 18 combine6Insn
        mc_step step_combine6 hc 19 combine6Insn
        mc_step step_combine6 hc 20 combine6Insn
        mc_step step_combine6 hc 21 combine6Insn
        mc_step step_combine6 hc 22 combine6Insn
        mc_step step_combine6 hc 23 combine6Insn
        exact Arm64.run_zero _ _
      · simp only [Arm64.ArmState.getW, Arm64.RegFile.get] at hb hacc ⊢
        rw [hx0, hb, hacc]
        refine ⟨?_, rfl, ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
           rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · by_cases h2 : (2 : UInt64) ≤ n <;> simp only [h2, ↓reduceIte] <;> rfl
        · simp [Crc32c.hwMul]
        · rw [toUInt32_toUInt64, csel_odd_bit]
          by_cases h1 : n &&& 1 = 1 <;> simp [h1, Crc32c.hwMul]
    rcases hstep16 with ⟨s1, hrun1, hpc1, hx01, hb1, hacc1, hx1, hx2, hx3, hx4, hx5, hx6, hmem1, hcs1⟩
    rw [hwPowGo_step_eq b acc n (by omega)]
    by_cases h2 : 2 ≤ n.toNat
    · have h2u : (2 : UInt64) ≤ n := h2
      simp only [h2u, ↓reduceIte] at hpc1
      simp only [h2, ↓reduceIte]
      have hsh : (n >>> 1).toNat = k / 2 := by rw [UInt64.toNat_shiftRight, hk]; rfl
      have hrec := ih (k / 2) (by omega) s1 (n >>> 1) (Crc32c.hwMul b b)
        (if n &&& 1 = 1 then Crc32c.hwMul acc b else acc)
        (hmem1 ▸ hc) hpc1 hx01 hb1 hacc1 hsh (by omega)
      refine run_bind_exists hrun1 ?_
      rcases hrec with ⟨steps2, s2, hrun2, hpc2, hr8, hx1', hx2', hx3', hx4', hx5', hx6', hmem2, hcs2⟩
      exact ⟨steps2, s2, hrun2, hpc2, hr8,
        hx1'.trans hx1, hx2'.trans hx2, hx3'.trans hx3,
        hx4'.trans hx4, hx5'.trans hx5, hx6'.trans hx6,
        hmem2.trans hmem1, hcs1.trans hcs2⟩
    · have h2u : ¬ (2 : UInt64) ≤ n := h2
      simp only [h2u, ↓reduceIte] at hpc1
      simp only [h2, ↓reduceIte]
      exact ⟨16, s1, hrun1, hpc1, hacc1, hx1, hx2, hx3, hx4, hx5, hx6, hmem1, hcs1⟩

private theorem combine6_pow_loop_cps {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {n : UInt64} {b acc : UInt32} {P : Arm64.ArmState → Prop}
    (hc : CodeLoaded code s.mem L)
    (hpc : s.pc = L.combine6Base + 32)
    (hx0 : s.regs.x0 = n)
    (hb : s.getW r9 = b)
    (hacc : s.getW r8 = acc)
    (hn : 1 ≤ n.toNat)
    (hcont : ∀ s', s'.pc = L.combine6Base + 96 →
      s'.getW r8 = Crc32c.hwPowGo b acc n →
      s'.regs.x1 = s.regs.x1 → s'.regs.x2 = s.regs.x2 → s'.regs.x3 = s.regs.x3 →
      s'.regs.x4 = s.regs.x4 → s'.regs.x5 = s.regs.x5 → s'.regs.x6 = s.regs.x6 →
      s'.mem = s.mem → CalleeSaved s s' →
      ∃ k s2, Arm64.run code k s' = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  rcases combine6_pow_loop n.toNat s n b acc hc hpc hx0 hb hacc rfl hn with
    ⟨k1, s', hr1, hpc', hr8', hx1', hx2', hx3', hx4', hx5', hx6', hmem', hcs'⟩
  exact run_bind_exists hr1 (hcont s' hpc' hr8' hx1' hx2' hx3' hx4' hx5' hx6' hmem' hcs')

/-! ### Exported machine-code specifications: `combine3_mc_spec` and `combine6_mc_spec` -/

private theorem usize_lt_512_iff (ws : USize) :
    (ws.toUInt64 < 0x200) ↔ (ws < 512) := by
  have e512 : (512 : USize).toNat = 512 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat, h]
  have eu64 : ws.toUInt64.toNat = ws.toNat := USize.toNat_toUInt64 ws
  change ws.toUInt64.toNat < 512 ↔ _
  rw [eu64, USize.lt_iff_toNat_lt, e512]

/-- Machine-code specification of `_lp_leancrc32c_Crc32c_combine3`:
executes from `L.combine3Base` to caller return address `s.regs.x30`, placing
`Crc32c.combine3 ws s0 s1 s2` in `W0`, with zero stack writes (`s'.mem = s.mem`)
and full AAPCS64 register preservation (`CalleeSaved s s'`). -/
theorem combine3_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {ws : USize} {s0 s1 s2 : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hpc : s.pc = L.combine3Base)
    (hws : s.regs.x0 = ws.toUInt64)
    (hs0 : s.getW r1 = s0)
    (hs1 : s.getW r2 = s1)
    (hs2 : s.getW r3 = s2) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.combine3 ws s0 s1 s2 ∧
      s'.mem = s.mem ∧
      CalleeSaved s s' := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hws hs0 hs1 hs2 ⊢
  subst hpc
  let s : Arm64.ArmState := { regs, sp, simd, nzcv, pc := L.combine3Base, mem }
  have hshift : ∃ s1, (∃ k1, Arm64.run code k1 s = some s1) ∧
      s1.pc = L.combine3Base + 120 ∧
      s1.getW r8 = Crc32c.hwShiftWords ws ∧
      s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
      s1.mem = s.mem ∧ CalleeSaved s s1 := by
    by_cases hlt : ws < 512
    · have hltu : ws.toUInt64 < 0x200 := (usize_lt_512_iff ws).mpr hlt
      have hws_nat : ws.toNat < 512 := by
        have := (usize_lt_512_iff ws).mpr hlt
        change ws.toUInt64.toNat < 512 at this
        simpa [USize.toNat_toUInt64] using this
      have hgot25 : Arm64.GotPairAt code s.mem (L.combine3Base + 100) L.hwShiftSmallAddr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine3.2.2 { idx := 25, rd := r8, target := .gHwShiftSmallBytes } (by decide)
      have htblPtr := Arm64.Mem.hasROU64_readU64LE hg.tblPtr
      have htblRead := tblBytes_read_hwShiftSmall hg ws hws_nat
      suffices hex : ∃ k1 s1, Arm64.run code k1 s = some s1 ∧
          (s1.pc = L.combine3Base + 120 ∧
           s1.getW r8 = Crc32c.hwShiftWords ws ∧
           s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
           s1.mem = s.mem ∧ CalleeSaved s s1) by
        rcases hex with ⟨k1, s1, hr1, hp⟩
        exact ⟨s1, ⟨k1, hr1⟩, hp⟩
      dsimp only [s]
      mc_step_ex step_combine3 hc 0 combine3Insn
      mc_step_ex_with step_combine3 hc 1 combine3Insn [hws, hltu]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot25
      mc_step_ex_with step_combine3 hc 27 combine3Insn [htblPtr]
      mc_step_ex step_combine3 hc 28 combine3Insn
      mc_step_ex_with step_combine3 hc 29 combine3Insn [hws, htblRead]
      refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, rfl, rfl, rfl, rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      simp [Crc32c.hwShiftWords, hlt, Arm64.ArmState.getW, Arm64.RegFile.get]
    · have hnltu : ¬ (ws.toUInt64 < 0x200) := fun h => hlt ((usize_lt_512_iff ws).mp h)
      have h1 : 1 ≤ ws.toUInt64.toNat := by
        have : ¬ ws.toUInt64.toNat < 512 := hnltu
        omega
      have hgot2 : Arm64.GotPairAt code s.mem (L.combine3Base + 8) L.hwX64Addr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine3.2.2 { idx := 2, rd := r8, target := .gHwX64 } (by decide)
      have hgot5 : Arm64.GotPairAt code s.mem (L.combine3Base + 20) L.hwOneAddr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine3.2.2 { idx := 5, rd := r8, target := .gHwOne } (by decide)
      have hreadX64 := Arm64.Mem.hasROU32_readU32LE hg.hwX64
      have hreadOne := Arm64.Mem.hasROU32_readU32LE hg.hwOne
      suffices hex : ∃ k1 s1, Arm64.run code k1 s = some s1 ∧
          (s1.pc = L.combine3Base + 120 ∧
           s1.getW r8 = Crc32c.hwShiftWords ws ∧
           s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
           s1.mem = s.mem ∧ CalleeSaved s s1) by
        rcases hex with ⟨k1, s1, hr1, hp⟩
        exact ⟨s1, ⟨k1, hr1⟩, hp⟩
      dsimp only [s]
      mc_step_ex step_combine3 hc 0 combine3Insn
      mc_step_ex_with step_combine3 hc 1 combine3Insn [hws, hnltu]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot2
      mc_step_ex_with step_combine3 hc 4 combine3Insn [hreadX64]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot5
      mc_step_ex_with step_combine3 hc 7 combine3Insn [hreadOne]
      apply combine3_pow_loop_cps hc rfl hws rfl rfl h1
      intro sl hpcl hr8l hx1l hx2l hx3l hmeml hcsl
      rcases sl with ⟨_, _, _, _, _, _⟩
      dsimp only at hpcl hr8l hx1l hx2l hx3l hmeml
      subst hpcl hmeml
      mc_step_ex step_combine3 hc 24 combine3Insn
      refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, hx1l, hx2l, hx3l, rfl,
        ⟨hcsl.sp, hcsl.x19, hcsl.x20, hcsl.x21, hcsl.x22, hcsl.x23, hcsl.x24,
         hcsl.x25, hcsl.x26, hcsl.x27, hcsl.x28, hcsl.x29, hcsl.x30,
         hcsl.d8, hcsl.d9, hcsl.d10, hcsl.d11, hcsl.d12, hcsl.d13, hcsl.d14, hcsl.d15⟩⟩
      simp only [Crc32c.hwShiftWords, hlt]
      simpa [Arm64.ArmState.getW, Arm64.RegFile.get] using hr8l
  rcases hshift with ⟨s1, ⟨k1, hr1⟩, hpc1, hf, hx1, hx2, hx3, hmem1, hcs1⟩
  refine run_bind_exists hr1 ?_
  rcases s1 with ⟨_, _, _, _, _, _⟩
  dsimp only at hpc1 hf hx1 hx2 hx3 hmem1
  subst hpc1 hmem1
  mc_step_ex step_combine3 hc 30 combine3Insn
  mc_step_ex step_combine3 hc 31 combine3Insn
  mc_step_ex step_combine3 hc 32 combine3Insn
  mc_step_ex step_combine3 hc 33 combine3Insn
  mc_step_ex step_combine3 hc 34 combine3Insn
  mc_step_ex step_combine3 hc 35 combine3Insn
  mc_step_ex step_combine3 hc 36 combine3Insn
  mc_step_ex step_combine3 hc 37 combine3Insn
  mc_step_ex step_combine3 hc 38 combine3Insn
  mc_step_ex step_combine3 hc 39 combine3Insn
  mc_step_ex step_combine3 hc 40 combine3Insn
  mc_step_ex step_combine3 hc 41 combine3Insn
  mc_step_ex step_combine3 hc 42 combine3Insn
  mc_step_ex step_combine3 hc 43 combine3Insn
  refine ⟨0, _, Arm64.run_zero _ _, ?_, ?_, rfl, ?_⟩
  · exact hcs1.x30
  · simp only [Arm64.ArmState.getW, Arm64.RegFile.get] at hs0 hs1 hs2 hf ⊢
    rw [hx1, hx2, hx3, hs0, hs1, hs2, hf]
    simp only [toUInt32_toUInt64, hwMul_fold, Crc32c.combine3]
  · exact hcs1.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Machine-code specification of `_lp_leancrc32c_Crc32c_combine6`:
executes from `L.combine6Base` to caller return address `s.regs.x30`, placing
`Crc32c.combine6 ws s0 s1 s2 s3 s4 s5` in `W0`, with zero stack writes (`s'.mem = s.mem`)
and full AAPCS64 register preservation (`CalleeSaved s s'`). -/
theorem combine6_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {ws : USize} {s0 s1 s2 s3 s4 s5 : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hpc : s.pc = L.combine6Base)
    (hws : s.regs.x0 = ws.toUInt64)
    (hs0 : s.getW r1 = s0)
    (hs1 : s.getW r2 = s1)
    (hs2 : s.getW r3 = s2)
    (hs3 : s.getW r4 = s3)
    (hs4 : s.getW r5 = s4)
    (hs5 : s.getW r6 = s5) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.combine6 ws s0 s1 s2 s3 s4 s5 ∧
      s'.mem = s.mem ∧
      CalleeSaved s s' := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hws hs0 hs1 hs2 hs3 hs4 hs5 ⊢
  subst hpc
  let s : Arm64.ArmState := { regs, sp, simd, nzcv, pc := L.combine6Base, mem }
  have hshift : ∃ s1, (∃ k1, Arm64.run code k1 s = some s1) ∧
      s1.pc = L.combine6Base + 120 ∧
      s1.getW r8 = Crc32c.hwShiftWords ws ∧
      s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
      s1.regs.x4 = s.regs.x4 ∧ s1.regs.x5 = s.regs.x5 ∧ s1.regs.x6 = s.regs.x6 ∧
      s1.mem = s.mem ∧ CalleeSaved s s1 := by
    by_cases hlt : ws < 512
    · have hltu : ws.toUInt64 < 0x200 := (usize_lt_512_iff ws).mpr hlt
      have hws_nat : ws.toNat < 512 := by
        have := (usize_lt_512_iff ws).mpr hlt
        change ws.toUInt64.toNat < 512 at this
        simpa [USize.toNat_toUInt64] using this
      have hgot25 : Arm64.GotPairAt code s.mem (L.combine6Base + 100) L.hwShiftSmallAddr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine6.2.2 { idx := 25, rd := r8, target := .gHwShiftSmallBytes } (by decide)
      have htblPtr := Arm64.Mem.hasROU64_readU64LE hg.tblPtr
      have htblRead := tblBytes_read_hwShiftSmall hg ws hws_nat
      suffices hex : ∃ k1 s1, Arm64.run code k1 s = some s1 ∧
          (s1.pc = L.combine6Base + 120 ∧
           s1.getW r8 = Crc32c.hwShiftWords ws ∧
           s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
           s1.regs.x4 = s.regs.x4 ∧ s1.regs.x5 = s.regs.x5 ∧ s1.regs.x6 = s.regs.x6 ∧
           s1.mem = s.mem ∧ CalleeSaved s s1) by
        rcases hex with ⟨k1, s1, hr1, hp⟩
        exact ⟨s1, ⟨k1, hr1⟩, hp⟩
      dsimp only [s]
      mc_step_ex step_combine6 hc 0 combine6Insn
      mc_step_ex_with step_combine6 hc 1 combine6Insn [hws, hltu]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot25
      mc_step_ex_with step_combine6 hc 27 combine6Insn [htblPtr]
      mc_step_ex step_combine6 hc 28 combine6Insn
      mc_step_ex_with step_combine6 hc 29 combine6Insn [hws, htblRead]
      refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      simp [Crc32c.hwShiftWords, hlt, Arm64.ArmState.getW, Arm64.RegFile.get]
    · have hnltu : ¬ (ws.toUInt64 < 0x200) := fun h => hlt ((usize_lt_512_iff ws).mp h)
      have h1 : 1 ≤ ws.toUInt64.toNat := by
        have : ¬ ws.toUInt64.toNat < 512 := hnltu
        omega
      have hgot2 : Arm64.GotPairAt code s.mem (L.combine6Base + 8) L.hwX64Addr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine6.2.2 { idx := 2, rd := r8, target := .gHwX64 } (by decide)
      have hgot5 : Arm64.GotPairAt code s.mem (L.combine6Base + 20) L.hwOneAddr r8 := by
        simpa [CodeLayout.symAddr, r8] using
          hc.combine6.2.2 { idx := 5, rd := r8, target := .gHwOne } (by decide)
      have hreadX64 := Arm64.Mem.hasROU32_readU32LE hg.hwX64
      have hreadOne := Arm64.Mem.hasROU32_readU32LE hg.hwOne
      suffices hex : ∃ k1 s1, Arm64.run code k1 s = some s1 ∧
          (s1.pc = L.combine6Base + 120 ∧
           s1.getW r8 = Crc32c.hwShiftWords ws ∧
           s1.regs.x1 = s.regs.x1 ∧ s1.regs.x2 = s.regs.x2 ∧ s1.regs.x3 = s.regs.x3 ∧
           s1.regs.x4 = s.regs.x4 ∧ s1.regs.x5 = s.regs.x5 ∧ s1.regs.x6 = s.regs.x6 ∧
           s1.mem = s.mem ∧ CalleeSaved s s1) by
        rcases hex with ⟨k1, s1, hr1, hp⟩
        exact ⟨s1, ⟨k1, hr1⟩, hp⟩
      dsimp only [s]
      mc_step_ex step_combine6 hc 0 combine6Insn
      mc_step_ex_with step_combine6 hc 1 combine6Insn [hws, hnltu]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot2
      mc_step_ex_with step_combine6 hc 4 combine6Insn [hreadX64]
      apply run_gotPair_exists
      · simpa [UInt64.add_assoc] using hgot5
      mc_step_ex_with step_combine6 hc 7 combine6Insn [hreadOne]
      apply combine6_pow_loop_cps hc rfl hws rfl rfl h1
      intro sl hpcl hr8l hx1l hx2l hx3l hx4l hx5l hx6l hmeml hcsl
      rcases sl with ⟨_, _, _, _, _, _⟩
      dsimp only at hpcl hr8l hx1l hx2l hx3l hx4l hx5l hx6l hmeml
      subst hpcl hmeml
      mc_step_ex step_combine6 hc 24 combine6Insn
      refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, hx1l, hx2l, hx3l, hx4l, hx5l, hx6l, rfl,
        ⟨hcsl.sp, hcsl.x19, hcsl.x20, hcsl.x21, hcsl.x22, hcsl.x23, hcsl.x24,
         hcsl.x25, hcsl.x26, hcsl.x27, hcsl.x28, hcsl.x29, hcsl.x30,
         hcsl.d8, hcsl.d9, hcsl.d10, hcsl.d11, hcsl.d12, hcsl.d13, hcsl.d14, hcsl.d15⟩⟩
      simp only [Crc32c.hwShiftWords, hlt]
      simpa [Arm64.ArmState.getW, Arm64.RegFile.get] using hr8l
  rcases hshift with ⟨s1, ⟨k1, hr1⟩, hpc1, hf, hx1, hx2, hx3, hx4, hx5, hx6, hmem1, hcs1⟩
  refine run_bind_exists hr1 ?_
  rcases s1 with ⟨_, _, _, _, _, _⟩
  dsimp only at hpc1 hf hx1 hx2 hx3 hx4 hx5 hx6 hmem1
  subst hpc1 hmem1
  mc_step_ex step_combine6 hc 30 combine6Insn
  mc_step_ex step_combine6 hc 31 combine6Insn
  mc_step_ex step_combine6 hc 32 combine6Insn
  mc_step_ex step_combine6 hc 33 combine6Insn
  mc_step_ex step_combine6 hc 34 combine6Insn
  mc_step_ex step_combine6 hc 35 combine6Insn
  mc_step_ex step_combine6 hc 36 combine6Insn
  mc_step_ex step_combine6 hc 37 combine6Insn
  mc_step_ex step_combine6 hc 38 combine6Insn
  mc_step_ex step_combine6 hc 39 combine6Insn
  mc_step_ex step_combine6 hc 40 combine6Insn
  mc_step_ex step_combine6 hc 41 combine6Insn
  mc_step_ex step_combine6 hc 42 combine6Insn
  mc_step_ex step_combine6 hc 43 combine6Insn
  mc_step_ex step_combine6 hc 44 combine6Insn
  mc_step_ex step_combine6 hc 45 combine6Insn
  mc_step_ex step_combine6 hc 46 combine6Insn
  mc_step_ex step_combine6 hc 47 combine6Insn
  mc_step_ex step_combine6 hc 48 combine6Insn
  mc_step_ex step_combine6 hc 49 combine6Insn
  mc_step_ex step_combine6 hc 50 combine6Insn
  mc_step_ex step_combine6 hc 51 combine6Insn
  mc_step_ex step_combine6 hc 52 combine6Insn
  mc_step_ex step_combine6 hc 53 combine6Insn
  mc_step_ex step_combine6 hc 54 combine6Insn
  mc_step_ex step_combine6 hc 55 combine6Insn
  mc_step_ex step_combine6 hc 56 combine6Insn
  mc_step_ex step_combine6 hc 57 combine6Insn
  mc_step_ex step_combine6 hc 58 combine6Insn
  mc_step_ex step_combine6 hc 59 combine6Insn
  mc_step_ex step_combine6 hc 60 combine6Insn
  mc_step_ex step_combine6 hc 61 combine6Insn
  mc_step_ex step_combine6 hc 62 combine6Insn
  mc_step_ex step_combine6 hc 63 combine6Insn
  mc_step_ex step_combine6 hc 64 combine6Insn
  refine ⟨0, _, Arm64.run_zero _ _, ?_, ?_, rfl, ?_⟩
  · exact hcs1.x30
  · simp only [Arm64.ArmState.getW, Arm64.RegFile.get] at hs0 hs1 hs2 hs3 hs4 hs5 hf ⊢
    rw [hx1, hx2, hx3, hx4, hx5, hx6, hs0, hs1, hs2, hs3, hs4, hs5, hf]
    simp only [toUInt32_toUInt64, hwMul_fold, Crc32c.combine6]
    ac_rfl
  · exact hcs1.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Crc32c.Arm64MC
