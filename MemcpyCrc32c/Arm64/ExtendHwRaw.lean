/-
Machine-code verification of `_lp_leancrc32c_Crc32c_extendHwRaw___redArg`
(`427` instructions, `Hw.c.o`), the entry point of the hardware CRC32C call
graph, against the frozen Phase 1 specification `Crc32c.Spec.extend`.

Two regimes:
- `len < 96`: the loop-free decision tree, proven per length in the generated
  `ExtendHwRawShort.lean`. Frameless: no memory is written.
- `96 ≤ len`: a `0x10`-byte frame (`x29`, `x30`), a call to
  `rawExtendHwMulti` (`0x150` bytes of stack below that), then `mvn` and
  return. Uses `rawExtendHwMulti_mc_spec`.

Kernel-checked without `bv_decide`.
-/
import MemcpyCrc32c.Arm64.ExtendHwRawShort
import MemcpyCrc32c.CApi

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Linking the kernel-level result to the Lean function and the spec -/

/-- The Lean function `extendHwRaw` as a conditioned `rawExtend` over the first `len` bytes. -/
theorem extendHwRaw_eq_rawExtend (c : UInt32) (a : ByteArray) (len : USize)
    (hs : a.size < USize.size) (h : len.toNat ≤ a.size) :
    Crc32c.extendHwRaw c a len hs h =
      Crc32c.rawExtend (c ^^^ 0xFFFFFFFF) (Crc32c.bytes a 0 len.toNat) ^^^ 0xFFFFFFFF := by
  have z : (0 : USize).toNat = 0 := by simp
  rw [Crc32c.extendHwRaw_eq_rawExtendHwUSize]
  simp only [Crc32c.rawExtendHwUSize_eq, z, Nat.zero_add]

/-- The same value as the frozen polynomial specification. -/
theorem rawExtend_conditioned_eq_spec (c : UInt32) (a : ByteArray) (len : USize)
    (hs : a.size < USize.size) (h : len.toNat ≤ a.size) :
    Crc32c.rawExtend (c ^^^ 0xFFFFFFFF) (Crc32c.bytes a 0 len.toNat) ^^^ 0xFFFFFFFF =
      Crc32c.Spec.extend c (a.extract 0 len.toNat) := by
  rw [← extendHwRaw_eq_rawExtend c a len hs h, Crc32c.extendHwRaw_spec]

/-! ### `len < 96`: frameless decision tree -/

/-- Machine-code specification of `extendHwRaw` for `len < 96`. No stack is
needed and no memory is written (`s'.mem = s.mem`); only payload bytes
`[objPtr + 0x18, objPtr + 0x18 + len)` are read. -/
theorem extendHwRaw_short_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {len : USize} (hlen : len.toNat ≤ a.size) (hlt : len.toNat < 96) {c : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = L.extendHwRawBase)
    (hw0 : s.getW r0 = c)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = len.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.Spec.extend c (a.extract 0 len.toNat) ∧
      s'.mem = s.mem ∧
      CalleeSaved s s' := by
  have hus := usize_le_2pow64
  have hlen64 : len.toUInt64 = len.toNat.toUInt64 :=
    u64_ext (by rw [USize.toNat_toUInt64, nat_toUInt64_toNat len.toNat (by omega)])
  rcases short_all len.toNat hlt hs hc hro hpc hw0 hx1 (hx2.trans hlen64) hlen with
    ⟨k, s', hrun, hpc', hr0, hmem, hcs⟩
  exact ⟨k, s', hrun, hpc', hr0.trans (rawExtend_conditioned_eq_spec c a len hs hlen), hmem, hcs⟩

/-! ### `96 ≤ len`: `0x10`-byte frame around a call to `rawExtendHwMulti` -/

theorem sp_pre_0x10 (sp : UInt64) : sp + 0xfffffffffffffff0 = sp - 0x10 := by
  rw [← UInt64.toBitVec_inj]
  change sp.toBitVec + 0xfffffffffffffff0#64 = sp.toBitVec - 0x10#64
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem sp_sub_0x10_sub_0x150 (sp : UInt64) : (sp - 0x10) - 0x150 = sp - 0x160 := by
  rw [← UInt64.toBitVec_inj]
  simp only [UInt64.toBitVec_sub]
  rw [BitVec.sub_sub]
  rfl

/-- Machine-code specification of `extendHwRaw` for `96 ≤ len`, with `.rw` stack
`[s.sp - 0x160, s.sp)`: `0x10` bytes for this function's frame and `0x150` for
`rawExtendHwMulti` and its callees. -/
theorem extendHwRaw_long_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {len : USize} (hlen : len.toNat ≤ a.size) (h96 : 96 ≤ len.toNat) {c : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = L.extendHwRawBase)
    (hsp_lo : 0x160 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x160) 0x160)
    (hw0 : s.getW r0 = c)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = len.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.Spec.extend c (a.extract 0 len.toNat) ∧
      StackDelta code L s.mem s'.mem (s.sp - 0x160) 0x160 ∧
      CalleeSaved s s' := by
  have hus := usize_le_2pow64
  have : UInt64.size = 2 ^ 64 := rfl
  have e96 : (96 : USize).toNat = 96 := by simp
  have z : (0 : USize).toNat = 0 := by simp
  have h96u : (96 : USize) ≤ len := USize.le_iff_toNat_le.mpr (by omega)
  have hsp_160 : (s.sp - 0x160).toNat = s.sp.toNat - 0x160 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x160 ≤ s.sp.toNat; omega)
  have hsp_10 : (s.sp - 0x10).toNat = s.sp.toNat - 0x10 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x10 ≤ s.sp.toNat; omega)
  have hrw_10 : s.mem.isRWRange (s.sp - 0x10) 0x10 := isRWRange_sub hrw (by omega) (by omega)
  have d_full0 := StackDelta.refl hrw hc hg
  have hb27 : BranchAt code (L.extendHwRawBase + 108) L.rawExtendHwMultiBase true := by
    simpa [CodeLayout.symAddr] using
      hc.extendHwRaw.2.1 { idx := 27, isCall := true, target := .fnRawExtendHwMulti } (by decide)
  have hhi : (0x5f : UInt64) < len.toUInt64 := by
    change (95 : Nat) < len.toUInt64.toNat
    rw [USize.toNat_toUInt64]; omega
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hro hpc hsp_lo hrw hx1 hx2 hsp_160 hsp_10 hrw_10 d_full0 ⊢
  dsimp only [getW_mk_r0] at hw0
  subst hpc
  have d0 := StackDelta.refl hrw_10 hc hg
  have w0 := writeU64LE_sp_zero d0.rwRange regs.x29
  have d1 := d0.step64_zero regs.x29
  have w1 := writeU64LE_sp_off d1.rwRange 8 regs.x30
  have d2 := d1.step64 8 regs.x30
  have hb := d2.rwRange.1
  have hsave29 : (((mem.writeSlot64 (sp - 0x10) regs.x29).writeSlot64 (sp - 0x10 + 8) regs.x30).readU64LE
      (sp - 0x10)) = some regs.x29 := by
    solve_slot_read hb
  have hsave30 : (((mem.writeSlot64 (sp - 0x10) regs.x29).writeSlot64 (sp - 0x10 + 8) regs.x30).readU64LE
      (sp - 0x10 + 8)) = some regs.x30 := by
    solve_slot_read hb
  mc_step_ex_with step_extendHwRaw hc 0 extendHwRawInsn [hx2]
  mc_step_ex step_extendHwRaw hc 1 extendHwRawInsn
  mc_step_ex_with step_extendHwRaw hc 2 extendHwRawInsn [hx2]
  mc_step_ex_with step_extendHwRaw hc 3 extendHwRawInsn [hhi]
  mc_step_ex_with step_extendHwRaw hc 23 extendHwRawInsn [sp_pre_0x10, w0, w1]
  mc_step_ex step_extendHwRaw d2.codeLoaded 24 extendHwRawInsn
  mc_step_ex step_extendHwRaw d2.codeLoaded 25 extendHwRawInsn
  mc_step_ex step_extendHwRaw d2.codeLoaded 26 extendHwRawInsn
  apply run_branch_call_at hb27
  dsimp only [setX_mk_r30]
  apply let_cur_state
  intro sCall
  have hsub_eq : sCall.sp - 0x150 = sp - 0x160 := sp_sub_0x10_sub_0x150 sp
  have d_full1 : StackDelta code L mem sCall.mem (sp - 0x160) 0x160 :=
    d_full0.trans_sub d2 (by omega) (by omega)
  have hrw_m : sCall.mem.isRWRange (sCall.sp - 0x150) 0x150 := by
    rw [hsub_eq]
    exact isRWRange_sub d_full1.rwRange (by omega) (by omega)
  have hro1 : sCall.mem.hasROBytes (objPtr + 0x18) a := d_full1.hasROBytes hro
  rcases rawExtendHwMulti_mc_spec (s := sCall) (uoff := 0) (ulen := len)
      (s_in := c ^^^ 0xFFFFFFFF) hs (by rw [z]; omega) h96u
      d2.codeLoaded d2.globalsLoaded hro1 rfl
      (by dsimp only [sCall]; omega) hrw_m
      (by dsimp only [sCall, getW_mk_r0]; rw [toUInt32_toUInt64, hw0])
      hx1 rfl rfl with
    ⟨kM, sM, hrM, hpcM, hr0M, d_m, hcsM⟩
  apply run_bind_exists hrM
  rw [hsub_eq] at d_m
  have d_full2 : StackDelta code L mem sM.mem (sp - 0x160) 0x160 :=
    d_full1.trans_sub d_m (by omega) (by omega)
  have hc2 := d_m.codeLoaded
  have hsave29M : sM.mem.readU64LE (sp - 0x10) = some regs.x29 :=
    (d_m.outside.readU64LE (sp - 0x10) (by omega) (by omega)).trans hsave29
  have hsave30M : sM.mem.readU64LE (sp - 0x10 + 8) = some regs.x30 := by
    have h8 : (sp - 0x10 + 8).toNat = (sp - 0x10).toNat + 8 := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change (sp - 0x10).toNat + 8 < 2 ^ 64; omega)]
      rfl
    exact (d_m.outside.readU64LE (sp - 0x10 + 8) (by omega) (by omega)).trans hsave30
  have hpcM' : sM.pc = L.extendHwRawBase + 112 :=
    hpcM.trans (by dsimp only [sCall]; simp only [UInt64.add_assoc]; rfl)
  have hspM : sM.sp = sp - 0x10 := hcsM.sp
  have hsp_restore : (sp - 0x10) + 0x10 = sp := u64_sub_add_cancel sp 0x10
  rcases sM with ⟨regsM, spM, simdM, nzcvM, pcM, memM⟩
  dsimp only at d_full2 hc2 hsave29M hsave30M hpcM' hspM
  dsimp only [getW_mk_r0] at hr0M
  subst hpcM' hspM
  mc_step_ex step_extendHwRaw hc2 28 extendHwRawInsn
  mc_step_ex_with step_extendHwRaw hc2 29 extendHwRawInsn [hsave29M, hsave30M, hsp_restore]
  mc_step_ex step_extendHwRaw hc2 30 extendHwRawInsn
  refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, d_full2,
    ⟨rfl, hcsM.x19, hcsM.x20, hcsM.x21, hcsM.x22, hcsM.x23, hcsM.x24,
     hcsM.x25, hcsM.x26, hcsM.x27, hcsM.x28, rfl, rfl,
     hcsM.d8, hcsM.d9, hcsM.d10, hcsM.d11, hcsM.d12, hcsM.d13, hcsM.d14, hcsM.d15⟩⟩
  rw [← rawExtend_conditioned_eq_spec c a len hs hlen]
  simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64]
  rw [hr0M, z, Nat.zero_add]

/-! ### Exported machine-code specification: `extendHwRaw_mc_spec` -/

/-- Machine-code specification of `_lp_leancrc32c_Crc32c_extendHwRaw___redArg`
(`427` instructions) and, through its callees, of the whole hardware CRC32C call
graph (`7` functions, `1137` instructions).

From any state `s` at `L.extendHwRawBase` with the code and constants loaded,
`.ro` payload `a` at `objPtr + 0x18`, `.rw` stack `[s.sp - 0x160, s.sp)`,
`W0 = c`, `X1 = objPtr` and `X2 = len` (`len ≤ a.size`), execution terminates
at the return address `s.regs.x30` with:
- `W0 = Crc32c.Spec.extend c (a.extract 0 len)`, the frozen Phase 1 polynomial
  specification (see `extendHwRaw_mc_eq_lean` for the Lean function),
- `StackDelta`: memory outside `[s.sp - 0x160, s.sp)` unchanged, every `.ro`
  byte and every unmapped byte preserved, and
- `CalleeSaved s s'`: `SP`, `X19..X30` and `D8..D15` preserved (AAPCS64).

Since the model's `step` fails on any read of an unmapped byte or write to a
non-`.rw` byte, termination also shows that the code never reads outside the
payload, the constants and its own stack. -/
theorem extendHwRaw_mc_spec {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {len : USize} (hlen : len.toNat ≤ a.size) {c : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = L.extendHwRawBase)
    (hsp_lo : 0x160 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x160) 0x160)
    (hw0 : s.getW r0 = c)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = len.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.Spec.extend c (a.extract 0 len.toNat) ∧
      StackDelta code L s.mem s'.mem (s.sp - 0x160) 0x160 ∧
      CalleeSaved s s' := by
  by_cases hlt : len.toNat < 96
  · rcases extendHwRaw_short_mc_spec hs hlen hlt hc hro hpc hw0 hx1 hx2 with
      ⟨k, s', hrun, hpc', hr0, hmem, hcs⟩
    exact ⟨k, s', hrun, hpc', hr0, hmem.symm ▸ StackDelta.refl hrw hc hg, hcs⟩
  · exact extendHwRaw_long_mc_spec hs hlen (by omega) hc hg hro hpc hsp_lo hrw hw0 hx1 hx2

/-- The same result stated against the Lean function the binary was compiled from. -/
theorem extendHwRaw_mc_eq_lean {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {len : USize} (hlen : len.toNat ≤ a.size) {c : UInt32}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = L.extendHwRawBase)
    (hsp_lo : 0x160 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x160) 0x160)
    (hw0 : s.getW r0 = c)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = len.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.extendHwRaw c a len hs hlen ∧
      StackDelta code L s.mem s'.mem (s.sp - 0x160) 0x160 ∧
      CalleeSaved s s' := by
  rcases extendHwRaw_mc_spec hs hlen hc hg hro hpc hsp_lo hrw hw0 hx1 hx2 with
    ⟨k, s', hrun, hpc', hr0, hd, hcs⟩
  exact ⟨k, s', hrun, hpc', hr0.trans (Crc32c.extendHwRaw_spec c a len hs hlen).symm, hd, hcs⟩

end Crc32c.Arm64MC
