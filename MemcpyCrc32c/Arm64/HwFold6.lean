/-
Machine-code verification of `_lp_leancrc32c_Crc32c_hwFold6Loop___redArg` (`197` instructions)
and `_lp_leancrc32c_Crc32c_hwFold6___redArg` (`186` instructions) from `Hw.c.o`
against `Crc32c.hwFold6Loop`, `Crc32c.hwFold6`, and `Crc32c.rawExtend`.

Also provides reusable permissioned stack-frame (`MemOutsideEq`, `StackDelta`) and
64-byte `.ro` block-load (`Block512Reads`) abstractions shared with downstream
callers (`RawExtendHwMulti`, `ExtendHwRaw`). Kernel-checked without `bv_decide`.
-/
import MemcpyCrc32c.Arm64.Combine
import MemcpyCrc32c.Arm64.HwLoop

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Section 1: `Fin.mk` SIMD lane/permute bridges & local stepping macros -/

theorem lane64_mk0 (v : V128) (h : 0 < 2) :
    V128.lane64 v ⟨0, h⟩ = V128.lo64 v :=
  Arm64.lane64_zero_simp v

theorem lane64_mk1 (v : V128) (h : 1 < 2) :
    V128.lane64 v ⟨1, h⟩ = V128.hi64 v :=
  Arm64.lane64_one_simp v

theorem insLane64_mk0_ofHalves (a0 a1 v : UInt64) (h : 0 < 2) :
    Arm64.insLane64 (V128.ofHalves a0 a1) ⟨0, h⟩ v = V128.ofHalves v a1 :=
  Arm64.insLane64_zero_ofHalves a0 a1 v

theorem insLane64_mk1_ofHalves (a0 a1 v : UInt64) (h : 1 < 2) :
    Arm64.insLane64 (V128.ofHalves a0 a1) ⟨1, h⟩ v = V128.ofHalves a0 v :=
  Arm64.insLane64_one_ofHalves a0 a1 v

theorem vextq_mk8_ofHalves (a0 a1 b0 b1 : UInt64) (h : 8 < 16) :
    Model.vextq (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) ⟨8, h⟩ =
      V128.ofHalves a1 b0 :=
  Arm64.vextq_8_ofHalves a0 a1 b0 b1

theorem getW_mk_r0 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r0 = regs.x0.toUInt32 := rfl
theorem getW_mk_r1 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r1 = regs.x1.toUInt32 := rfl
theorem getW_mk_r2 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r2 = regs.x2.toUInt32 := rfl
theorem getW_mk_r3 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r3 = regs.x3.toUInt32 := rfl
theorem getW_mk_r4 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r4 = regs.x4.toUInt32 := rfl
theorem getW_mk_r5 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r5 = regs.x5.toUInt32 := rfl
theorem getW_mk_r6 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r6 = regs.x6.toUInt32 := rfl
theorem getW_mk_r8 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r8 = regs.x8.toUInt32 := rfl
theorem getW_mk_r9 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r9 = regs.x9.toUInt32 := rfl
theorem getW_mk_r10 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r10 = regs.x10.toUInt32 := rfl
theorem getW_mk_r11 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r11 = regs.x11.toUInt32 := rfl
theorem getW_mk_r12 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r12 = regs.x12.toUInt32 := rfl
theorem getW_mk_r13 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r13 = regs.x13.toUInt32 := rfl
theorem getW_mk_r14 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r14 = regs.x14.toUInt32 := rfl
theorem getW_mk_r15 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r15 = regs.x15.toUInt32 := rfl
theorem getW_mk_r22 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).getW r22 = regs.x22.toUInt32 := rfl
theorem setX_mk_r30 (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (pc : UInt64) (mem : Arm64.Mem) (v : UInt64) :
    (Arm64.ArmState.mk regs sp simd nzcv pc mem).setX r30 v =
      Arm64.ArmState.mk { regs with x30 := v } sp simd nzcv pc mem := rfl

theorem u64_sub_add_cancel (a b : UInt64) : (a - b) + b = a := by
  rw [← UInt64.toBitVec_inj]
  simp

theorem sp_pre_0x60 (sp : UInt64) : sp + 0xffffffffffffffa0 = sp - 0x60 := by
  rw [← UInt64.toBitVec_inj]
  change sp.toBitVec + 0xffffffffffffffa0#64 = sp.toBitVec - 0x60#64
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem sub_0x60_add (sp c d : UInt64) (h : 0x60 + d = c := by rfl) :
    (sp - 0x60) + c = sp + d := by
  subst h
  rw [← UInt64.add_assoc, u64_sub_add_cancel]

theorem run_gotPair_at {code : UInt64 → Option UInt32}
    {s : Arm64.ArmState} {addr symAddr : UInt64} {rd : Arm64.RegIdx}
    {P : Arm64.ArmState → Prop}
    (hg : Arm64.GotPairAt code s.mem addr symAddr rd)
    (hpc : s.pc = addr := by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)
    (hrest : ∃ n s2, Arm64.run code n { (s.setX rd symAddr) with pc := addr + 8 } = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  have hg' : Arm64.GotPairAt code s.mem s.pc symAddr rd := by rw [hpc]; exact hg
  have hst : { (s.setX rd symAddr) with pc := s.pc + 8 } =
      { (s.setX rd symAddr) with pc := addr + 8 } := by rw [hpc]
  exact run_bind_exists ((Arm64.run_gotPair hg').trans (congrArg some hst)) hrest

theorem run_branch_call_at {code : UInt64 → Option UInt32}
    {s : Arm64.ArmState} {addr calleeBase : UInt64}
    {P : Arm64.ArmState → Prop}
    (hb : BranchAt code addr calleeBase true)
    (hpc : s.pc = addr := by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)
    (hrest : ∃ n s2, Arm64.run code n { (s.setX r30 (addr + 4)) with pc := calleeBase } = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  have hb' : BranchAt code s.pc calleeBase true := by rw [hpc]; exact hb
  have hst : { (s.setX r30 (s.pc + 4)) with pc := calleeBase } =
      { (s.setX r30 (addr + 4)) with pc := calleeBase } := by rw [hpc]
  exact run_step_exists ((step_branch_call hb').trans (congrArg some hst)) hrest

theorem run_branch_jump_at {code : UInt64 → Option UInt32}
    {s : Arm64.ArmState} {addr calleeBase : UInt64}
    {P : Arm64.ArmState → Prop}
    (hb : BranchAt code addr calleeBase false)
    (hpc : s.pc = addr := by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)
    (hrest : ∃ n s2, Arm64.run code n { s with pc := calleeBase } = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  have hb' : BranchAt code s.pc calleeBase false := by rw [hpc]; exact hb
  exact run_step_exists (step_branch_jump hb') hrest

theorem let_cur_state {code : UInt64 → Option UInt32} {s : Arm64.ArmState}
    {P : Arm64.ArmState → Prop}
    (h : let st := s; ∃ k s', Arm64.run code k st = some s' ∧ P s') :
    ∃ k s', Arm64.run code k s = some s' ∧ P s' := h

macro "f6_gotPair" gp:term : tactic =>
  `(tactic| (
      apply run_gotPair_at $gp
      dsimp only [Arm64.ArmState.setX, Arm64.RegFile.set, CodeLayout.symAddr,
        r0, r1, r2, r3, r8, r9, r17, r20, r21, r25, r28]))

theorem run_bind_of_setup {code : UInt64 → Option UInt32} {s : Arm64.ArmState}
    {Q P : Arm64.ArmState → Prop}
    (h1 : ∃ m s1, Arm64.run code m s = some s1 ∧ Q s1)
    (h2 : ∀ s1, Q s1 → ∃ n s2, Arm64.run code n s1 = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  rcases h1 with ⟨m, s1, hm, hq⟩
  exact run_bind_exists hm (h2 s1 hq)

macro "f6_step" step_thm:ident hc:ident idx:num insn_fn:ident : tactic =>
  `(tactic| mc_step_with $step_thm $hc $idx $insn_fn
      [lane64_mk0, lane64_mk1, insLane64_mk0_ofHalves, insLane64_mk1_ofHalves, vextq_mk8_ofHalves])

macro "f6_step_with" step_thm:ident hc:ident idx:num insn_fn:ident
    "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| mc_step_with $step_thm $hc $idx $insn_fn
      [lane64_mk0, lane64_mk1, insLane64_mk0_ofHalves, insLane64_mk1_ofHalves, vextq_mk8_ofHalves, $extras,*])

macro "f6_step_ex" step_thm:ident hc:ident idx:num insn_fn:ident : tactic =>
  `(tactic| mc_step_ex_with $step_thm $hc $idx $insn_fn
      [lane64_mk0, lane64_mk1, insLane64_mk0_ofHalves, insLane64_mk1_ofHalves, vextq_mk8_ofHalves])

macro "f6_step_ex_with" step_thm:ident hc:ident idx:num insn_fn:ident
    "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| mc_step_ex_with $step_thm $hc $idx $insn_fn
      [lane64_mk0, lane64_mk1, insLane64_mk0_ofHalves, insLane64_mk1_ofHalves, vextq_mk8_ofHalves, $extras,*])

/-! ### Section 2: Stack-frame invariance (`MemOutsideEq`, `StackDelta`) & slot readbacks -/

/-- Memory `m'` agrees with `m` at every byte address outside `[lo.toNat, lo.toNat + len)`. -/
def MemOutsideEq (m m' : Arm64.Mem) (lo : UInt64) (len : Nat) : Prop :=
  ∀ a : UInt64, (a.toNat < lo.toNat ∨ lo.toNat + len ≤ a.toNat) → m' a = m a

theorem MemOutsideEq.refl (m : Arm64.Mem) (lo : UInt64) (len : Nat) :
    MemOutsideEq m m lo len := fun _ _ => rfl

theorem MemOutsideEq.trans {m1 m2 m3 : Arm64.Mem} {lo : UInt64} {len : Nat}
    (h12 : MemOutsideEq m1 m2 lo len) (h23 : MemOutsideEq m2 m3 lo len) :
    MemOutsideEq m1 m3 lo len :=
  fun a ha => (h23 a ha).trans (h12 a ha)

theorem MemOutsideEq.mono {m m' : Arm64.Mem} {subLo lo : UInt64} {subLen len : Nat}
    (h : MemOutsideEq m m' subLo subLen)
    (h1 : lo.toNat ≤ subLo.toNat) (h2 : subLo.toNat + subLen ≤ lo.toNat + len) :
    MemOutsideEq m m' lo len :=
  fun a ha => h a (by omega)

theorem MemOutsideEq.writeSlot64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64) :
    MemOutsideEq m (m.writeSlot64 (lo + off.toUInt64) v) lo len := by
  intro a ha
  have : UInt64.size = 2 ^ 64 := rfl
  have hoff_nat : (lo + off.toUInt64).toNat = lo.toNat + off := by
    rw [UInt64.toNat_add, nat_toUInt64_toNat off (by omega), Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.writeSlot64_outside m (lo + off.toUInt64) a v (by omega) (by omega)

theorem MemOutsideEq.writeSlot32 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32) :
    MemOutsideEq m (m.writeSlot32 (lo + off.toUInt64) v) lo len := by
  intro a ha
  have : UInt64.size = 2 ^ 64 := rfl
  have hoff_nat : (lo + off.toUInt64).toNat = lo.toNat + off := by
    rw [UInt64.toNat_add, nat_toUInt64_toNat off (by omega), Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.writeSlot32_outside m (lo + off.toUInt64) a v (by omega) (by omega)

theorem MemOutsideEq.readU32LE {m m' : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hout : MemOutsideEq m m' lo len) (raddr : UInt64)
    (hr : raddr.toNat + 4 ≤ UInt64.size)
    (hdisj : raddr.toNat + 4 ≤ lo.toNat ∨ lo.toNat + len ≤ raddr.toNat) :
    m'.readU32LE raddr = m.readU32LE raddr := by
  have eqd (d : UInt64) (hd : decide (d.toNat < 4) = true := by decide) :
      m'.readU8 (raddr + d) = m.readU8 (raddr + d) := by
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (raddr + d).toNat = raddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [Arm64.Mem.readU8, hout (raddr + d) (by omega)]
  have e0 : m'.readU8 raddr = m.readU8 raddr := by simpa using eqd 0
  simp only [Arm64.Mem.readU32LE, e0, eqd 1, eqd 2, eqd 3]

theorem MemOutsideEq.readU64LE {m m' : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hout : MemOutsideEq m m' lo len) (raddr : UInt64)
    (hr : raddr.toNat + 8 ≤ UInt64.size)
    (hdisj : raddr.toNat + 8 ≤ lo.toNat ∨ lo.toNat + len ≤ raddr.toNat) :
    m'.readU64LE raddr = m.readU64LE raddr := by
  have eqd (d : UInt64) (hd : decide (d.toNat < 8) = true := by decide) :
      m'.readU8 (raddr + d) = m.readU8 (raddr + d) := by
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (raddr + d).toNat = raddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [Arm64.Mem.readU8, hout (raddr + d) (by omega)]
  have e0 : m'.readU8 raddr = m.readU8 raddr := by simpa using eqd 0
  simp only [Arm64.Mem.readU64LE, e0, eqd 1, eqd 2, eqd 3, eqd 4, eqd 5, eqd 6, eqd 7]

theorem isRWRange_sub {m : Arm64.Mem} {lo subLo : UInt64} {len subLen : Nat}
    (hrw : m.isRWRange lo len)
    (h1 : lo.toNat ≤ subLo.toNat) (h2 : subLo.toNat + subLen ≤ lo.toNat + len) :
    m.isRWRange subLo subLen := by
  have hb := hrw.1
  have : UInt64.size = 2 ^ 64 := rfl
  refine ⟨by omega, fun k hk => ?_⟩
  let d := subLo.toNat - lo.toNat + k
  have heq : subLo + k.toUInt64 = lo + d.toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_add, UInt64.toNat_add,
      nat_toUInt64_toNat k (by omega), nat_toUInt64_toNat d (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [heq]
  exact hrw.2 d (by omega)

/-- Composable postcondition bundle for `.rw` stack-frame writes in `[lo, lo + len)`:
preserves all addresses outside `[lo, lo + len)`, keeps `[lo, lo + len)` writable,
preserves all `.ro` bytes (input buffers + constants) and `none` bytes (guard pages),
and maintains `CodeLoaded` and `GlobalsLoaded`. -/
structure StackDelta (code : UInt64 → Option UInt32) (L : CodeLayout)
    (m m' : Arm64.Mem) (lo : UInt64) (len : Nat) : Prop where
  outside       : MemOutsideEq m m' lo len
  rwRange       : m'.isRWRange lo len
  roPres        : ∀ a b, m a = some (.ro, b) → m' a = some (.ro, b)
  nonePres      : ∀ a, m a = none → m' a = none
  codeLoaded    : CodeLoaded code m' L
  globalsLoaded : GlobalsLoaded m' L

theorem StackDelta.refl {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (hc : CodeLoaded code m L) (hg : GlobalsLoaded m L) :
    StackDelta code L m m lo len where
  outside       := MemOutsideEq.refl m lo len
  rwRange       := hrw
  roPres        := fun _ _ h => h
  nonePres      := fun _ h => h
  codeLoaded    := hc
  globalsLoaded := hg

theorem StackDelta.hasROBytes {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m m' : Arm64.Mem} {lo : UInt64} {len : Nat}
    (d : StackDelta code L m m' lo len) {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) : m'.hasROBytes base bs :=
  ⟨hro.1, fun k hk => d.roPres _ _ (hro.2 k hk)⟩

theorem StackDelta.step64 {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m m1 : Arm64.Mem} {lo : UInt64} {len : Nat}
    (d : StackDelta code L m m1 lo len) (off : UInt64) (v : UInt64)
    (hoff : off.toNat + 8 ≤ len := by decide) :
    StackDelta code L m (m1.writeSlot64 (lo + off) v) lo len := by
  have heq : off = off.toNat.toUInt64 := u64_ext (by simp [Nat.toUInt64])
  rw [heq]
  exact {
    outside       := d.outside.trans (MemOutsideEq.writeSlot64 d.rwRange.1 off.toNat hoff v)
    rwRange       := Arm64.Mem.writeSlot64_isRWRange d.rwRange _ v
    roPres        := fun _ _ h => Arm64.Mem.writeSlot64_preserves_ro d.rwRange off.toNat hoff v (d.roPres _ _ h)
    nonePres      := fun _ h => Arm64.Mem.writeSlot64_preserves_none d.rwRange off.toNat hoff v (d.nonePres _ h)
    codeLoaded    := d.codeLoaded.preserves_writeSlot64 d.rwRange off.toNat hoff v
    globalsLoaded := d.globalsLoaded.preserves_writeSlot64 d.rwRange off.toNat hoff v
  }

theorem StackDelta.step32 {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m m1 : Arm64.Mem} {lo : UInt64} {len : Nat}
    (d : StackDelta code L m m1 lo len) (off : UInt64) (v : UInt32)
    (hoff : off.toNat + 4 ≤ len := by decide) :
    StackDelta code L m (m1.writeSlot32 (lo + off) v) lo len := by
  have heq : off = off.toNat.toUInt64 := u64_ext (by simp [Nat.toUInt64])
  rw [heq]
  exact {
    outside       := d.outside.trans (MemOutsideEq.writeSlot32 d.rwRange.1 off.toNat hoff v)
    rwRange       := Arm64.Mem.writeSlot32_isRWRange d.rwRange _ v
    roPres        := fun _ _ h => Arm64.Mem.writeSlot32_preserves_ro d.rwRange off.toNat hoff v (d.roPres _ _ h)
    nonePres      := fun _ h => Arm64.Mem.writeSlot32_preserves_none d.rwRange off.toNat hoff v (d.nonePres _ h)
    codeLoaded    := d.codeLoaded.preserves_writeSlot32 d.rwRange off.toNat hoff v
    globalsLoaded := d.globalsLoaded.preserves_writeSlot32 d.rwRange off.toNat hoff v
  }

theorem StackDelta.trans_sub {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m m1 m2 : Arm64.Mem} {lo subLo : UInt64} {len subLen : Nat}
    (d1 : StackDelta code L m m1 lo len)
    (d2 : StackDelta code L m1 m2 subLo subLen)
    (h1 : lo.toNat ≤ subLo.toNat) (h2 : subLo.toNat + subLen ≤ lo.toNat + len) :
    StackDelta code L m m2 lo len where
  outside := d1.outside.trans (d2.outside.mono h1 h2)
  rwRange := by
    have hb := d1.rwRange.1
    have : UInt64.size = 2 ^ 64 := rfl
    refine ⟨hb, fun k hk => ?_⟩
    have hk_addr : (lo + k.toUInt64).toNat = lo.toNat + k := by
      rw [UInt64.toNat_add, nat_toUInt64_toNat k (by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases hin : subLo.toNat ≤ lo.toNat + k ∧ lo.toNat + k < subLo.toNat + subLen
    · let sk := lo.toNat + k - subLo.toNat
      have heq : lo + k.toUInt64 = subLo + sk.toUInt64 := by
        apply u64_ext
        rw [hk_addr, UInt64.toNat_add, nat_toUInt64_toNat sk (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [heq]
      exact d2.rwRange.2 sk (by omega)
    · rw [d2.outside (lo + k.toUInt64) (by omega)]
      exact d1.rwRange.2 k hk
  roPres        := fun _ _ h => d2.roPres _ _ (d1.roPres _ _ h)
  nonePres      := fun _ h => d2.nonePres _ (d1.nonePres _ h)
  codeLoaded    := d2.codeLoaded
  globalsLoaded := d2.globalsLoaded

theorem StackDelta.step64_zero {code : UInt64 → Option UInt32} {L : CodeLayout}
    {m m1 : Arm64.Mem} {lo : UInt64} {len : Nat}
    (d : StackDelta code L m m1 lo len) (v : UInt64)
    (hoff : 8 ≤ len := by decide) :
    StackDelta code L m (m1.writeSlot64 lo v) lo len := by
  simpa only [UInt64.add_zero] using d.step64 0 v hoff

theorem writeU64LE_sp_zero {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (v : UInt64) (hlen : 8 ≤ len := by decide) :
    m.writeU64LE lo v = some (m.writeSlot64 lo v) := by
  have h := Arm64.Mem.writeU64LE_of_isRWRange hrw 0 (by omega) v
  simpa only [nat_toUInt64_zero, UInt64.add_zero] using h

theorem writeU64LE_sp_off {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : UInt64) (v : UInt64)
    (hoff : off.toNat + 8 ≤ len := by decide) :
    m.writeU64LE (lo + off) v = some (m.writeSlot64 (lo + off) v) := by
  have heq : off = off.toNat.toUInt64 := u64_ext (by simp [Nat.toUInt64])
  rw [heq]
  exact Arm64.Mem.writeU64LE_of_isRWRange hrw off.toNat hoff v

theorem writeU32LE_sp_off {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : UInt64) (v : UInt32)
    (hoff : off.toNat + 4 ≤ len := by decide) :
    m.writeU32LE (lo + off) v = some (m.writeSlot32 (lo + off) v) := by
  have heq : off = off.toNat.toUInt64 := u64_ext (by simp [Nat.toUInt64])
  rw [heq]
  exact Arm64.Mem.writeU32LE_of_isRWRange hrw off.toNat hoff v

theorem readU64LE_writeSlot64_same_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt64}
    (hok : decide (wOff = rOff ∧ wOff.toNat + 8 ≤ len) = true) :
    (m.writeSlot64 (lo + wOff) v).readU64LE (lo + rOff) = some v := by
  have hp := of_decide_eq_true hok
  rcases hp with ⟨rfl, hwlen⟩
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot64_same m (lo + wOff) v (by omega)

theorem readU64LE_writeSlot64_ne_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt64}
    (hok : decide (wOff.toNat + 8 ≤ len ∧ rOff.toNat + 8 ≤ len ∧
      (rOff.toNat + 8 ≤ wOff.toNat ∨ wOff.toNat + 8 ≤ rOff.toNat)) = true) :
    (m.writeSlot64 (lo + wOff) v).readU64LE (lo + rOff) = m.readU64LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot64_disjoint m (lo + wOff) (lo + rOff) v
    (by omega) (by omega) (by omega)

theorem readU32LE_writeSlot64_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt64}
    (hok : decide (wOff.toNat + 8 ≤ len ∧ rOff.toNat + 4 ≤ len ∧
      (rOff.toNat + 4 ≤ wOff.toNat ∨ wOff.toNat + 8 ≤ rOff.toNat)) = true) :
    (m.writeSlot64 (lo + wOff) v).readU32LE (lo + rOff) = m.readU32LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU32LE_writeSlot64_disjoint m (lo + wOff) (lo + rOff) v
    (by omega) (by omega) (by omega)

theorem readU64LE_writeSlot32_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt32}
    (hok : decide (wOff.toNat + 4 ≤ len ∧ rOff.toNat + 8 ≤ len ∧
      (rOff.toNat + 8 ≤ wOff.toNat ∨ wOff.toNat + 4 ≤ rOff.toNat)) = true) :
    (m.writeSlot32 (lo + wOff) v).readU64LE (lo + rOff) = m.readU64LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot32_disjoint m (lo + wOff) (lo + rOff) v
    (by omega) (by omega) (by omega)

theorem readU64LE_writeSlot64_zero_same_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {v : UInt64}
    (hok : decide (8 ≤ len) = true) :
    (m.writeSlot64 lo v).readU64LE lo = some v := by
  have hp := of_decide_eq_true hok
  exact Arm64.Mem.readU64LE_writeSlot64_same m lo v (by omega)

theorem readU64LE_writeSlot64_zero_ne_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {rOff : UInt64} {v : UInt64}
    (hok : decide (8 ≤ rOff.toNat ∧ rOff.toNat + 8 ≤ len) = true) :
    (m.writeSlot64 lo v).readU64LE (lo + rOff) = m.readU64LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot64_disjoint m lo (lo + rOff) v
    (by omega) (by omega) (by omega)

theorem readU32LE_writeSlot64_zero_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {rOff : UInt64} {v : UInt64}
    (hok : decide (8 ≤ rOff.toNat ∧ rOff.toNat + 4 ≤ len) = true) :
    (m.writeSlot64 lo v).readU32LE (lo + rOff) = m.readU32LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU32LE_writeSlot64_disjoint m lo (lo + rOff) v
    (by omega) (by omega) (by omega)

theorem readU64LE_zero_writeSlot64_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff : UInt64} {v : UInt64}
    (hok : decide (8 ≤ wOff.toNat ∧ wOff.toNat + 8 ≤ len) = true) :
    (m.writeSlot64 (lo + wOff) v).readU64LE lo = m.readU64LE lo := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot64_disjoint m (lo + wOff) lo v
    (by omega) (by omega) (by omega)

theorem readU64LE_zero_writeSlot32_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff : UInt64} {v : UInt32}
    (hok : decide (8 ≤ wOff.toNat ∧ wOff.toNat + 4 ≤ len) = true) :
    (m.writeSlot32 (lo + wOff) v).readU64LE lo = m.readU64LE lo := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU64LE_writeSlot32_disjoint m (lo + wOff) lo v
    (by omega) (by omega) (by omega)

theorem readU32LE_writeSlot32_same_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt32}
    (hok : decide (wOff = rOff ∧ wOff.toNat + 8 ≤ len) = true) :
    (m.writeSlot32 (lo + wOff) v).readU32LE (lo + rOff) = some v := by
  have hp := of_decide_eq_true hok
  rcases hp with ⟨rfl, hwlen⟩
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact Arm64.Mem.readU32LE_writeSlot32_same m (lo + wOff) v (by omega)

theorem readU32LE_writeSlot32_ne_u64 {m : Arm64.Mem} {lo : UInt64} {len : Nat}
    (hb : lo.toNat + len ≤ UInt64.size) {wOff rOff : UInt64} {v : UInt32}
    (hok : decide (wOff.toNat + 4 ≤ len ∧ rOff.toNat + 4 ≤ len ∧
      (rOff.toNat + 4 ≤ wOff.toNat ∨ wOff.toNat + 4 ≤ rOff.toNat)) = true) :
    (m.writeSlot32 (lo + wOff) v).readU32LE (lo + rOff) = m.readU32LE (lo + rOff) := by
  have hp := of_decide_eq_true hok
  have : UInt64.size = 2 ^ 64 := rfl
  have hw : (lo + wOff).toNat = lo.toNat + wOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hr : (lo + rOff).toNat = lo.toNat + rOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have eqd (d : UInt64) (hd : decide (d.toNat < 4) = true := by decide) :
      (m.writeSlot32 (lo + wOff) v).readU8 ((lo + rOff) + d) = m.readU8 ((lo + rOff) + d) := by
    have hd' := of_decide_eq_true hd
    have ht : ((lo + rOff) + d).toNat = (lo + rOff).toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [Arm64.Mem.readU8,
      Arm64.Mem.writeSlot32_outside m (lo + wOff) ((lo + rOff) + d) v (by omega) (by omega)]
  have e0 : (m.writeSlot32 (lo + wOff) v).readU8 (lo + rOff) = m.readU8 (lo + rOff) := by
    simpa using eqd 0
  simp only [Arm64.Mem.readU32LE, e0, eqd 1, eqd 2, eqd 3]

macro "solve_slot_read" hb:ident : tactic =>
  `(tactic| repeat (first
      | (rw [readU64LE_writeSlot64_same_u64 $hb]; rotate_left; decide; try rfl)
      | (rw [readU64LE_writeSlot64_ne_u64 $hb]; rotate_left; decide)
      | (rw [readU64LE_writeSlot64_zero_same_u64 $hb]; rotate_left; decide; try rfl)
      | (rw [readU64LE_writeSlot64_zero_ne_u64 $hb]; rotate_left; decide)
      | (rw [readU64LE_zero_writeSlot64_u64 $hb]; rotate_left; decide)
      | (rw [readU64LE_zero_writeSlot32_u64 $hb]; rotate_left; decide)
      | (rw [readU32LE_writeSlot64_u64 $hb]; rotate_left; decide)
      | (rw [readU32LE_writeSlot64_zero_u64 $hb]; rotate_left; decide)
      | (rw [readU64LE_writeSlot32_u64 $hb]; rotate_left; decide)
      | (rw [readU32LE_writeSlot32_same_u64 $hb]; rotate_left; decide; try rfl)
      | (rw [readU32LE_writeSlot32_ne_u64 $hb]; rotate_left; decide)))

/-! ### Section 3: 64-byte `.ro` block reads (`b512w0..b512w7`) & PMULL fold identities -/

def b512w0 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  SimdModels.loadU64LE a p hs (by omega)

def b512w1 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  Crc32c.load64Hi a hs p (by omega)

def b512w2 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 16).toNat = p.toNat + 16 := Crc32c.usize_add_toNat p 16 (by omega)
  SimdModels.loadU64LE a (p + 16) hs (by omega)

def b512w3 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 16).toNat = p.toNat + 16 := Crc32c.usize_add_toNat p 16 (by omega)
  Crc32c.load64Hi a hs (p + 16) (by omega)

def b512w4 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 32).toNat = p.toNat + 32 := Crc32c.usize_add_toNat p 32 (by omega)
  SimdModels.loadU64LE a (p + 32) hs (by omega)

def b512w5 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 32).toNat = p.toNat + 32 := Crc32c.usize_add_toNat p 32 (by omega)
  Crc32c.load64Hi a hs (p + 32) (by omega)

def b512w6 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 48).toNat = p.toNat + 48 := Crc32c.usize_add_toNat p 48 (by omega)
  SimdModels.loadU64LE a (p + 48) hs (by omega)

def b512w7 (a : ByteArray) (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : UInt64 :=
  have _ : (p + 48).toNat = p.toNat + 48 := Crc32c.usize_add_toNat p 48 (by omega)
  Crc32c.load64Hi a hs (p + 48) (by omega)

theorem withBlock512_eq_b512 {α : Type} (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α) :
    Crc32c.withBlock512 a hs p hp k =
      k (b512w0 a hs p hp) (b512w1 a hs p hp) (b512w2 a hs p hp) (b512w3 a hs p hp)
        (b512w4 a hs p hp) (b512w5 a hs p hp) (b512w6 a hs p hp) (b512w7 a hs p hp) := rfl

theorem b512_crc512 (a : ByteArray) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) (s : UInt32) :
    SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
      (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
        s (b512w0 a hs p hp)) (b512w1 a hs p hp)) (b512w2 a hs p hp)) (b512w3 a hs p hp))
      (b512w4 a hs p hp)) (b512w5 a hs p hp)) (b512w6 a hs p hp)) (b512w7 a hs p hp) =
      Crc32c.crc512 a hs p hp s := rfl

structure Block512Reads (m : Arm64.Mem) (base : UInt64) (a : ByteArray)
    (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 64 ≤ a.size) : Prop where
  r0  : m.readU64LE (base + p.toUInt64) = some (b512w0 a hs p hp)
  r1  : m.readU64LE (base + (p.toUInt64 + 8)) = some (b512w1 a hs p hp)
  r2  : m.readU64LE (base + (p.toUInt64 + 0x10)) = some (b512w2 a hs p hp)
  r3  : m.readU64LE (base + (p.toUInt64 + (0x10 + 8))) = some (b512w3 a hs p hp)
  r4  : m.readU64LE (base + (p.toUInt64 + 0x20)) = some (b512w4 a hs p hp)
  r5  : m.readU64LE (base + (p.toUInt64 + (0x20 + 8))) = some (b512w5 a hs p hp)
  r6  : m.readU64LE (base + (p.toUInt64 + 0x30)) = some (b512w6 a hs p hp)
  r7  : m.readU64LE (base + (p.toUInt64 + (0x30 + 8))) = some (b512w7 a hs p hp)
  vq6 : m.readV128LE (base + (p.toUInt64 + 0x30)) =
          some (V128.ofHalves (b512w6 a hs p hp) (b512w7 a hs p hp))

theorem block512Reads_of_ro {m : Arm64.Mem} {base : UInt64} {a : ByteArray}
    (hro : m.hasROBytes base a) (hs : a.size < USize.size)
    (p : USize) (hp : p.toNat + 64 ≤ a.size) :
    Block512Reads m base a hs p hp := by
  have hus := usize_le_2pow64
  have off_eq (k : Nat) (hk : k ≤ 56) :
      have _ : (p + USize.ofNat k).toNat = p.toNat + k := Crc32c.usize_add_toNat p k (by omega)
      p.toUInt64 + k.toUInt64 = (p + USize.ofNat k).toUInt64 := by
    intro hpk
    apply u64_ext
    rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64, hpk,
      nat_toUInt64_toNat k (by omega), Nat.mod_eq_of_lt (by omega)]
  have p8  : (p + 8).toNat = p.toNat + 8   := Crc32c.usize_add_toNat p 8 (by omega)
  have p16 : (p + 16).toNat = p.toNat + 16 := Crc32c.usize_add_toNat p 16 (by omega)
  have p24 : (p + 24).toNat = p.toNat + 24 := Crc32c.usize_add_toNat p 24 (by omega)
  have p32 : (p + 32).toNat = p.toNat + 32 := Crc32c.usize_add_toNat p 32 (by omega)
  have p40 : (p + 40).toNat = p.toNat + 40 := Crc32c.usize_add_toNat p 40 (by omega)
  have p48 : (p + 48).toNat = p.toNat + 48 := Crc32c.usize_add_toNat p 48 (by omega)
  have p56 : (p + 56).toNat = p.toNat + 56 := Crc32c.usize_add_toNat p 56 (by omega)
  have e8  : p.toUInt64 + 8  = (p + 8).toUInt64  := off_eq 8 (by omega)
  have e16 : p.toUInt64 + 0x10 = (p + 16).toUInt64 := off_eq 16 (by omega)
  have e24 : p.toUInt64 + (0x10 + 8) = (p + 24).toUInt64 := off_eq 24 (by omega)
  have e32 : p.toUInt64 + 0x20 = (p + 32).toUInt64 := off_eq 32 (by omega)
  have e40 : p.toUInt64 + (0x20 + 8) = (p + 40).toUInt64 := off_eq 40 (by omega)
  have e48 : p.toUInt64 + 0x30 = (p + 48).toUInt64 := off_eq 48 (by omega)
  have e56 : p.toUInt64 + (0x30 + 8) = (p + 56).toUInt64 := off_eq 56 (by omega)
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e8u : (8 : USize).toNat = 8 := by simp
  have a24 : (p + 16) + 8 = p + 24 := USize.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
    change ((p + 16) + 8).toNat = (p + 24).toNat
    rw [USize.toNat_add, p16, p24, e8u]; exact Nat.mod_eq_of_lt (by omega)))
  have a40 : (p + 32) + 8 = p + 40 := USize.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
    change ((p + 32) + 8).toNat = (p + 40).toNat
    rw [USize.toNat_add, p32, p40, e8u]; exact Nat.mod_eq_of_lt (by omega)))
  have a56 : (p + 48) + 8 = p + 56 := USize.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
    change ((p + 48) + 8).toNat = (p + 56).toNat
    rw [USize.toNat_add, p48, p56, e8u]; exact Nat.mod_eq_of_lt (by omega)))
  have load_eq {i j : USize} (hij : i = j) (hi : i.toNat + 8 ≤ a.size) (hj : j.toNat + 8 ≤ a.size) :
      Model.loadU64LE a j hs hj = SimdModels.loadU64LE a i hs hi := by
    subst hij; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Arm64.Mem.hasROBytes_readU64LE hro hs p (by omega)
  · rw [e8]; exact Arm64.Mem.hasROBytes_readU64LE hro hs (p + 8) (by omega)
  · rw [e16]; exact Arm64.Mem.hasROBytes_readU64LE hro hs (p + 16) (by omega)
  · rw [e24]
    exact (Arm64.Mem.hasROBytes_readU64LE hro hs (p + 24) (by omega)).trans
      (congrArg some (load_eq a24 (by rw [a24, p24]; omega) (by omega)))
  · rw [e32]; exact Arm64.Mem.hasROBytes_readU64LE hro hs (p + 32) (by omega)
  · rw [e40]
    exact (Arm64.Mem.hasROBytes_readU64LE hro hs (p + 40) (by omega)).trans
      (congrArg some (load_eq a40 (by rw [a40, p40]; omega) (by omega)))
  · rw [e48]; exact Arm64.Mem.hasROBytes_readU64LE hro hs (p + 48) (by omega)
  · rw [e56]
    exact (Arm64.Mem.hasROBytes_readU64LE hro hs (p + 56) (by omega)).trans
      (congrArg some (load_eq a56 (by rw [a56, p56]; omega) (by omega)))
  · rw [e48]
    exact Arm64.Mem.hasROBytes_readV128LE hro hs (p + 48) (by omega)

private theorem fold512Lo_stream3 (a0 a1 w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    (((SimdModels.clmulLo w5 Crc32c.kFold128_2 ^^^ SimdModels.clmulLo w1 Crc32c.kFold384_2) ^^^
      (SimdModels.clmulLo w3 Crc32c.kFold256_2 ^^^ SimdModels.clmulLo a1 Crc32c.kFold512_2)) ^^^
     ((SimdModels.clmulLo w4 Crc32c.kFold128_1 ^^^ SimdModels.clmulLo w0 Crc32c.kFold384_1) ^^^
      (SimdModels.clmulLo w2 Crc32c.kFold256_1 ^^^ SimdModels.clmulLo a0 Crc32c.kFold512_1))) ^^^ w6 =
      Crc32c.fold512Lo a0 a1 w0 w1 w2 w3 w4 w5 w6 := by
  unfold Crc32c.fold512Lo Crc32c.init512Lo Crc32c.fold128Lo
  dsimp only
  ac_rfl

private theorem fold512Hi_stream3 (a0 a1 w0 w1 w2 w3 w4 w5 w7 : UInt64) :
    (((SimdModels.clmulHi w5 Crc32c.kFold128_2 ^^^ SimdModels.clmulHi w1 Crc32c.kFold384_2) ^^^
      (SimdModels.clmulHi w3 Crc32c.kFold256_2 ^^^ SimdModels.clmulHi a1 Crc32c.kFold512_2)) ^^^
     ((SimdModels.clmulHi w4 Crc32c.kFold128_1 ^^^ SimdModels.clmulHi w0 Crc32c.kFold384_1) ^^^
      (SimdModels.clmulHi w2 Crc32c.kFold256_1 ^^^ SimdModels.clmulHi a0 Crc32c.kFold512_1))) ^^^ w7 =
      Crc32c.fold512Hi a0 a1 w0 w1 w2 w3 w4 w5 w7 := by
  unfold Crc32c.fold512Hi Crc32c.init512Hi Crc32c.fold128Hi
  dsimp only
  ac_rfl

private theorem fold512Lo_eor3 (x0 x1 w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    (((((((w6 ^^^ SimdModels.clmulLo x0 Crc32c.kFold512_1) ^^^ SimdModels.clmulLo x1 Crc32c.kFold512_2) ^^^
      SimdModels.clmulLo w0 Crc32c.kFold384_1) ^^^ SimdModels.clmulLo w1 Crc32c.kFold384_2) ^^^
      SimdModels.clmulLo w2 Crc32c.kFold256_1) ^^^ SimdModels.clmulLo w3 Crc32c.kFold256_2) ^^^
      SimdModels.clmulLo w4 Crc32c.kFold128_1) ^^^ SimdModels.clmulLo w5 Crc32c.kFold128_2 =
      Crc32c.fold512Lo x0 x1 w0 w1 w2 w3 w4 w5 w6 :=
  rfl

private theorem fold512Hi_eor3 (x0 x1 w0 w1 w2 w3 w4 w5 w7 : UInt64) :
    (((((((w7 ^^^ SimdModels.clmulHi x0 Crc32c.kFold512_1) ^^^ SimdModels.clmulHi x1 Crc32c.kFold512_2) ^^^
      SimdModels.clmulHi w0 Crc32c.kFold384_1) ^^^ SimdModels.clmulHi w1 Crc32c.kFold384_2) ^^^
      SimdModels.clmulHi w2 Crc32c.kFold256_1) ^^^ SimdModels.clmulHi w3 Crc32c.kFold256_2) ^^^
      SimdModels.clmulHi w4 Crc32c.kFold128_1) ^^^ SimdModels.clmulHi w5 Crc32c.kFold128_2 =
      Crc32c.fold512Hi x0 x1 w0 w1 w2 w3 w4 w5 w7 :=
  rfl

/-! ### Section 4: `hwFold6Loop` machine-code verification (`197` instructions) -/

private structure SavedFrame6Loop (m : Arm64.Mem) (lo : UInt64) (orig : Arm64.ArmState) : Prop where
  sd9  : m.readU64LE lo = some (orig.getD r9)
  sd8  : m.readU64LE (lo + 0x08) = some (orig.getD r8)
  sx28 : m.readU64LE (lo + 0x10) = some orig.regs.x28
  sx27 : m.readU64LE (lo + (0x10 + 8)) = some orig.regs.x27
  sx26 : m.readU64LE (lo + 0x20) = some orig.regs.x26
  sx25 : m.readU64LE (lo + (0x20 + 8)) = some orig.regs.x25
  sx24 : m.readU64LE (lo + 0x30) = some orig.regs.x24
  sx23 : m.readU64LE (lo + (0x30 + 8)) = some orig.regs.x23
  sx22 : m.readU64LE (lo + 0x40) = some orig.regs.x22
  sx21 : m.readU64LE (lo + (0x40 + 8)) = some orig.regs.x21
  sx20 : m.readU64LE (lo + 0x50) = some orig.regs.x20
  sx19 : m.readU64LE (lo + (0x50 + 8)) = some orig.regs.x19

private theorem hwFold6Loop_prologue {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s : Arm64.ArmState}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hpc : s.pc = L.hwFold6LoopBase)
    (hsp : 0x60 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x60) 0x60) :
    ∃ mFrame : Arm64.Mem,
      Arm64.run code 6 s = some { s with
        sp := s.sp - 0x60
        pc := L.hwFold6LoopBase + 24
        mem := mFrame } ∧
      StackDelta code L s.mem mFrame (s.sp - 0x60) 0x60 ∧
      SavedFrame6Loop mFrame (s.sp - 0x60) s := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hsp hrw ⊢
  subst hpc
  have hpre : sp + 0xffffffffffffffa0 = sp - 0x60 := sp_pre_0x60 sp
  have hb : (sp - 0x60).toNat + 0x60 ≤ UInt64.size := hrw.1
  have d0 := StackDelta.refl hrw hc hg
  have w0 := writeU64LE_sp_zero d0.rwRange (V128.lo64 simd.v9)
  have d1 := d0.step64_zero (V128.lo64 simd.v9)
  have w1 := writeU64LE_sp_off d1.rwRange 0x08 (V128.lo64 simd.v8)
  have d2 := d1.step64 0x08 (V128.lo64 simd.v8)
  have w2 := writeU64LE_sp_off d2.rwRange 0x10 regs.x28
  have d3 := d2.step64 0x10 regs.x28
  have w3 := writeU64LE_sp_off d3.rwRange (0x10 + 8) regs.x27
  have d4 := d3.step64 (0x10 + 8) regs.x27
  have w4 := writeU64LE_sp_off d4.rwRange 0x20 regs.x26
  have d5 := d4.step64 0x20 regs.x26
  have w5 := writeU64LE_sp_off d5.rwRange (0x20 + 8) regs.x25
  have d6 := d5.step64 (0x20 + 8) regs.x25
  have w6 := writeU64LE_sp_off d6.rwRange 0x30 regs.x24
  have d7 := d6.step64 0x30 regs.x24
  have w7 := writeU64LE_sp_off d7.rwRange (0x30 + 8) regs.x23
  have d8 := d7.step64 (0x30 + 8) regs.x23
  have w8 := writeU64LE_sp_off d8.rwRange 0x40 regs.x22
  have d9 := d8.step64 0x40 regs.x22
  have w9 := writeU64LE_sp_off d9.rwRange (0x40 + 8) regs.x21
  have d10 := d9.step64 (0x40 + 8) regs.x21
  have w10 := writeU64LE_sp_off d10.rwRange 0x50 regs.x20
  have d11 := d10.step64 0x50 regs.x20
  have w11 := writeU64LE_sp_off d11.rwRange (0x50 + 8) regs.x19
  have d12 := d11.step64 (0x50 + 8) regs.x19
  refine ⟨_, ?_, d12, ?_⟩
  · f6_step_with step_hwFold6Loop hc 0 hwFold6LoopInsn [hpre, w0, w1]
    f6_step_with step_hwFold6Loop d2.codeLoaded 1 hwFold6LoopInsn [w2, w3]
    f6_step_with step_hwFold6Loop d4.codeLoaded 2 hwFold6LoopInsn [w4, w5]
    f6_step_with step_hwFold6Loop d6.codeLoaded 3 hwFold6LoopInsn [w6, w7]
    f6_step_with step_hwFold6Loop d8.codeLoaded 4 hwFold6LoopInsn [w8, w9]
    f6_step_with step_hwFold6Loop d10.codeLoaded 5 hwFold6LoopInsn [w10, w11]
    exact Arm64.run_zero _ _
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb

private theorem hwFold6Loop_epilogue {code : UInt64 → Option UInt32} {L : CodeLayout}
    {s orig : Arm64.ArmState} {ws : USize} {s0 s1 s2 : UInt32} {a0 a1 b0 b1 c0 c1 : UInt64}
    (hc : CodeLoaded code s.mem L)
    (hg : GlobalsLoaded s.mem L)
    (hpc : s.pc = L.hwFold6LoopBase + 716)
    (hsp : s.sp = orig.sp - 0x60)
    (hframe : SavedFrame6Loop s.mem (orig.sp - 0x60) orig)
    (hx10 : s.regs.x10 = ws.toUInt64)
    (hw1 : s.getW r1 = s0)
    (hw2 : s.getW r2 = s1)
    (hw3 : s.getW r3 = s2)
    (hx19 : s.regs.x19 = a0)
    (hx20 : s.regs.x20 = a1)
    (hv17 : s.simd.v17 = V128.ofHalves b0 b1)
    (hv16 : s.simd.v16 = V128.ofHalves c0 c1)
    (hx29 : s.regs.x29 = orig.regs.x29)
    (hx30 : s.regs.x30 = orig.regs.x30)
    (hd10 : s.getD r10 = orig.getD r10)
    (hd11 : s.getD r11 = orig.getD r11)
    (hd12 : s.getD r12 = orig.getD r12)
    (hd13 : s.getD r13 = orig.getD r13)
    (hd14 : s.getD r14 = orig.getD r14)
    (hd15 : s.getD r15 = orig.getD r15) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = orig.regs.x30 ∧
      s'.getW r0 = Crc32c.combine6 ws s0 s1 s2
        (Crc32c.finish128 a0 a1) (Crc32c.finish128 b0 b1) (Crc32c.finish128 c0 c1) ∧
      s'.mem = s.mem ∧
      CalleeSaved orig s' := by
  have hb196 := hc.hwFold6Loop.2.1 { idx := 196, isCall := false, target := .fnCombine6 } (by decide)
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hsp hframe hx10 hw1 hw2 hw3 hx19 hx20 hv17 hv16
  dsimp only at hx29 hx30 hd10 hd11 hd12 hd13 hd14 hd15 ⊢
  subst hpc hsp
  have hsp_restore : (orig.sp - 0x60) + 0x60 = orig.sp := u64_sub_add_cancel orig.sp 0x60
  f6_step_ex step_hwFold6Loop hc 179 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 180 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 181 hwFold6LoopInsn [hv17]
  f6_step_ex step_hwFold6Loop hc 182 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 183 hwFold6LoopInsn [hv17]
  f6_step_ex step_hwFold6Loop hc 184 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 185 hwFold6LoopInsn [hv16]
  f6_step_ex step_hwFold6Loop hc 186 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 187 hwFold6LoopInsn [hv16]
  f6_step_ex step_hwFold6Loop hc 188 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 189 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 190 hwFold6LoopInsn [hframe.sx20, hframe.sx19]
  f6_step_ex_with step_hwFold6Loop hc 191 hwFold6LoopInsn [hframe.sx22, hframe.sx21]
  f6_step_ex_with step_hwFold6Loop hc 192 hwFold6LoopInsn [hframe.sx24, hframe.sx23]
  f6_step_ex_with step_hwFold6Loop hc 193 hwFold6LoopInsn [hframe.sx26, hframe.sx25]
  f6_step_ex_with step_hwFold6Loop hc 194 hwFold6LoopInsn [hframe.sx28, hframe.sx27]
  f6_step_ex_with step_hwFold6Loop hc 195 hwFold6LoopInsn [hframe.sd9, hframe.sd8, hsp_restore]
  apply run_branch_jump_at hb196
  dsimp only [CodeLayout.symAddr]
  dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3] at hw1 hw2 hw3
  apply let_cur_state
  intro st
  rcases combine6_mc_spec (s := st) (ws := ws)
      (s0 := s0) (s1 := s1) (s2 := s2)
      (s3 := Crc32c.finish128 a0 a1)
      (s4 := Crc32c.finish128 b0 b1)
      (s5 := Crc32c.finish128 c0 c1)
      hc hg rfl hx10
      (by dsimp only [st, getW_mk_r1]; exact hw1)
      (by dsimp only [st, getW_mk_r2]; exact hw2)
      (by dsimp only [st, getW_mk_r3]; exact hw3)
      (by dsimp only [st, getW_mk_r4, Crc32c.finish128]; rw [hx19, hx20, toUInt32_toUInt64])
      (by dsimp only [st, getW_mk_r5, Crc32c.finish128]; exact toUInt32_toUInt64 _)
      (by dsimp only [st, getW_mk_r6, Crc32c.finish128]; exact toUInt32_toUInt64 _) with
    ⟨k2, s', hrun2, hpc2, hr0, hmem2, hcs2⟩
  refine ⟨k2, s', hrun2, ?_, hr0, hmem2, ?_⟩
  · exact hpc2.trans hx30
  · refine ⟨hcs2.sp, hcs2.x19, hcs2.x20, hcs2.x21, hcs2.x22, hcs2.x23, hcs2.x24,
      hcs2.x25, hcs2.x26, hcs2.x27, hcs2.x28, hcs2.x29.trans hx29, hcs2.x30.trans hx30,
      ?_, ?_, hcs2.d10.trans hd10, hcs2.d11.trans hd11, hcs2.d12.trans hd12,
      hcs2.d13.trans hd13, hcs2.d14.trans hd14, hcs2.d15.trans hd15⟩
    · exact hcs2.d8.trans (by dsimp only [st]; exact V128.lo64_ofHalves _ _)
    · exact hcs2.d9.trans (by dsimp only [st]; exact V128.lo64_ofHalves _ _)

private structure LoopConsts (s : Arm64.ArmState) (base : UInt64)
    (stop ws L L2 L3 L4 L5 : USize) : Prop where
  x13 : s.regs.x13 = base
  x4  : s.regs.x4  = base + L.toUInt64
  x5  : s.regs.x5  = base + L2.toUInt64
  x0  : s.regs.x0  = base + L3.toUInt64
  x17 : s.regs.x17 = base + L4.toUInt64
  x16 : s.regs.x16 = base + L5.toUInt64
  x8  : s.regs.x8  = stop.toUInt64
  x10 : s.regs.x10 = ws.toUInt64
  v0  : s.simd.v0  = V128.ofHalves Crc32c.kFold512_1 0
  v1  : s.simd.v1  = V128.ofHalves Crc32c.kFold512_2 0
  v2  : s.simd.v2  = V128.ofHalves Crc32c.kFold384_1 0
  v3  : s.simd.v3  = V128.ofHalves Crc32c.kFold384_2 0
  v4  : s.simd.v4  = V128.ofHalves Crc32c.kFold256_1 0
  v5  : s.simd.v5  = V128.ofHalves Crc32c.kFold256_2 0
  v6  : s.simd.v6  = V128.ofHalves Crc32c.kFold128_1 0
  v7  : s.simd.v7  = V128.ofHalves Crc32c.kFold128_2 0

private structure KeepMeta (s s' : Arm64.ArmState) : Prop where
  sp  : s'.sp = s.sp
  mem : s'.mem = s.mem
  x29 : s'.regs.x29 = s.regs.x29
  x30 : s'.regs.x30 = s.regs.x30
  d10 : s'.getD r10 = s.getD r10
  d11 : s'.getD r11 = s.getD r11
  d12 : s'.getD r12 = s.getD r12
  d13 : s'.getD r13 = s.getD r13
  d14 : s'.getD r14 = s.getD r14
  d15 : s'.getD r15 = s.getD r15

private theorem KeepMeta.refl (s : Arm64.ArmState) : KeepMeta s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem KeepMeta.trans {s1 s2 s3 : Arm64.ArmState}
    (h12 : KeepMeta s1 s2) (h23 : KeepMeta s2 s3) : KeepMeta s1 s3 :=
  ⟨h23.sp.trans h12.sp, h23.mem.trans h12.mem, h23.x29.trans h12.x29, h23.x30.trans h12.x30,
   h23.d10.trans h12.d10, h23.d11.trans h12.d11, h23.d12.trans h12.d12,
   h23.d13.trans h12.d13, h23.d14.trans h12.d14, h23.d15.trans h12.d15⟩

private theorem usize_add_toUInt64_eq {x y : USize} (h : (x + y).toNat = x.toNat + y.toNat) :
    y.toUInt64 + x.toUInt64 = (x + y).toUInt64 := by
  have hus := usize_le_2pow64
  have hxy : x.toNat + y.toNat < 2 ^ 64 := by
    have := (x + y).toNat_lt_size; omega
  apply u64_ext
  rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64,
    USize.toNat_toUInt64, h, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem hwFold6Loop_body_crc {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {i stop ws L L2 L3 L4 L5 : USize}
    (hi1 : (i + L).toNat = i.toNat + L.toNat)
    (hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat)
    (hi3 : (i + L3).toNat = i.toNat + 3 * L.toNat)
    (hL2 : L2.toNat = 2 * L.toNat)
    (hL3 : L3.toNat = 3 * L.toNat)
    (hc0 : i.toNat + 64 ≤ a.size)
    (hc1 : (i + L).toNat + 64 ≤ a.size)
    (hc2 : (i + L2).toNat + 64 ≤ a.size)
    {s0 s1 s2 : UInt32}
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hinv : LoopConsts s base stop ws L L2 L3 L4 L5)
    (hpc : s.pc = Layout.hwFold6LoopBase + 220)
    (hx9 : s.regs.x9 = i.toUInt64)
    (hw1 : s.getW r1 = s0)
    (hw2 : s.getW r2 = s1)
    (hw3 : s.getW r3 = s2) :
    ∃ st1, Arm64.run code 36 s = some st1 ∧
      st1.pc = Layout.hwFold6LoopBase + 364 ∧
      LoopConsts st1 base stop ws L L2 L3 L4 L5 ∧
      KeepMeta s st1 ∧
      st1.regs.x9 = i.toUInt64 ∧
      st1.regs.x6 = base + (i + L3).toUInt64 ∧
      st1.getW r1 = Crc32c.crc512 a hs i hc0 s0 ∧
      st1.getW r2 = Crc32c.crc512 a hs (i + L) hc1 s1 ∧
      st1.getW r22 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64
        (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 s2
          (b512w0 a hs (i + L2) hc2)) (b512w1 a hs (i + L2) hc2))
        (b512w2 a hs (i + L2) hc2)) (b512w3 a hs (i + L2) hc2) ∧
      st1.regs.x23 = b512w4 a hs (i + L2) hc2 ∧
      st1.regs.x24 = b512w5 a hs (i + L2) hc2 ∧
      st1.regs.x21 = b512w6 a hs (i + L2) hc2 ∧
      st1.regs.x3  = b512w7 a hs (i + L2) hc2 ∧
      st1.regs.x19 = s.regs.x19 ∧ st1.regs.x20 = s.regs.x20 ∧
      st1.regs.x15 = s.regs.x15 ∧ st1.regs.x14 = s.regs.x14 ∧
      st1.regs.x12 = s.regs.x12 ∧ st1.regs.x11 = s.regs.x11 := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  rcases hinv with ⟨hx13_i, hx4_i, hx5_i, hx0_i, hx17_i, hx16_i, hx8_i, hx10_i,
    hv0_i, hv1_i, hv2_i, hv3_i, hv4_i, hv5_i, hv6_i, hv7_i⟩
  dsimp only at hc hro hpc hx9 hw1 hw2 hw3 hx13_i hx4_i hx5_i hx0_i hx17_i hx16_i hx8_i hx10_i
  dsimp only at hv0_i hv1_i hv2_i hv3_i hv4_i hv5_i hv6_i hv7_i ⊢
  subst hpc
  have b0 := block512Reads_of_ro hro hs i hc0
  have b1 := block512Reads_of_ro hro hs (i + L) hc1
  have b2 := block512Reads_of_ro hro hs (i + L2) hc2
  have u1 : L.toUInt64 + i.toUInt64 = (i + L).toUInt64 := usize_add_toUInt64_eq hi1
  have u2 : L2.toUInt64 + i.toUInt64 = (i + L2).toUInt64 :=
    usize_add_toUInt64_eq (by omega)
  have u3 : L3.toUInt64 + i.toUInt64 = (i + L3).toUInt64 :=
    usize_add_toUInt64_eq (by omega)
  apply Exists.intro
  apply And.intro
  · f6_step_with step_hwFold6Loop hc 55 hwFold6LoopInsn [hx13_i, hx9]
    f6_step_with step_hwFold6Loop hc 56 hwFold6LoopInsn [b0.r0, b0.r1]
    f6_step step_hwFold6Loop hc 57 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 58 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 59 hwFold6LoopInsn [b0.r2, b0.r3]
    f6_step step_hwFold6Loop hc 60 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 61 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 62 hwFold6LoopInsn [b0.r4, b0.r5]
    f6_step step_hwFold6Loop hc 63 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 64 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 65 hwFold6LoopInsn [b0.r6, b0.r7]
    f6_step step_hwFold6Loop hc 66 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 67 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 68 hwFold6LoopInsn [hx4_i, hx9, u1]
    f6_step_with step_hwFold6Loop hc 69 hwFold6LoopInsn [b1.r0, b1.r1]
    f6_step step_hwFold6Loop hc 70 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 71 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 72 hwFold6LoopInsn [b1.r2, b1.r3]
    f6_step step_hwFold6Loop hc 73 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 74 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 75 hwFold6LoopInsn [b1.r4, b1.r5]
    f6_step step_hwFold6Loop hc 76 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 77 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 78 hwFold6LoopInsn [b1.r6, b1.r7]
    f6_step step_hwFold6Loop hc 79 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 80 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 81 hwFold6LoopInsn [hx5_i, hx9, u2]
    f6_step_with step_hwFold6Loop hc 82 hwFold6LoopInsn [b2.r0, b2.r1]
    f6_step step_hwFold6Loop hc 83 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 84 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 85 hwFold6LoopInsn [b2.r2, b2.r3]
    f6_step step_hwFold6Loop hc 86 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 87 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 88 hwFold6LoopInsn [b2.r4, b2.r5]
    f6_step_with step_hwFold6Loop hc 89 hwFold6LoopInsn [b2.r6, b2.r7]
    f6_step_with step_hwFold6Loop hc 90 hwFold6LoopInsn [hx0_i, hx9, u3]
    exact Arm64.run_zero _ _
  · dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3, getW_mk_r22] at hw1 hw2 hw3 ⊢
    rw [hw1, hw2, hw3, b512_crc512, b512_crc512]
    exact ⟨rfl,
      ⟨rfl, rfl, rfl, rfl, hx17_i, hx16_i, hx8_i, hx10_i,
       hv0_i, hv1_i, hv2_i, hv3_i, hv4_i, hv5_i, hv6_i, hv7_i⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, toUInt32_toUInt64 _, toUInt32_toUInt64 _, toUInt32_toUInt64 _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hwFold6Loop_body_s3 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {i stop ws L L2 L3 L4 L5 : USize}
    (h64 : (i + 64).toNat = i.toNat + 64)
    (hi4 : (i + L4).toNat = i.toNat + 4 * L.toNat)
    (hi5 : (i + L5).toNat = i.toNat + 5 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat)
    (hL5 : L5.toNat = 5 * L.toNat)
    (hc2 : (i + L2).toNat + 64 ≤ a.size)
    (hc3 : (i + L3).toNat + 64 ≤ a.size)
    (hc4 : (i + L4).toNat + 64 ≤ a.size)
    (hc5 : (i + L5).toNat + 64 ≤ a.size)
    {s2 : UInt32} {a0 a1 : UInt64}
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hinv : LoopConsts s base stop ws L L2 L3 L4 L5)
    (hpc : s.pc = Layout.hwFold6LoopBase + 364)
    (hx9 : s.regs.x9 = i.toUInt64)
    (hx6 : s.regs.x6 = base + (i + L3).toUInt64)
    (hw22 : s.getW r22 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64
        (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 s2
          (b512w0 a hs (i + L2) hc2)) (b512w1 a hs (i + L2) hc2))
        (b512w2 a hs (i + L2) hc2)) (b512w3 a hs (i + L2) hc2))
    (hx23 : s.regs.x23 = b512w4 a hs (i + L2) hc2)
    (hx24 : s.regs.x24 = b512w5 a hs (i + L2) hc2)
    (hx21 : s.regs.x21 = b512w6 a hs (i + L2) hc2)
    (hx3  : s.regs.x3  = b512w7 a hs (i + L2) hc2)
    (hx19 : s.regs.x19 = a0)
    (hx20 : s.regs.x20 = a1) :
    ∃ st1, Arm64.run code 43 s = some st1 ∧
      st1.pc = Layout.hwFold6LoopBase + 536 ∧
      LoopConsts st1 base stop ws L L2 L3 L4 L5 ∧
      KeepMeta s st1 ∧
      st1.regs.x9 = (i + 64).toUInt64 ∧
      st1.regs.x7 = base + (i + L4).toUInt64 ∧
      st1.regs.x6 = base + (i + L5).toUInt64 ∧
      st1.simd.v17 = V128.ofHalves (b512w6 a hs (i + L4) hc4) (b512w7 a hs (i + L4) hc4) ∧
      st1.simd.v16 = V128.ofHalves (b512w6 a hs (i + L5) hc5) (b512w7 a hs (i + L5) hc5) ∧
      st1.getW r1 = s.getW r1 ∧
      st1.getW r2 = s.getW r2 ∧
      st1.getW r3 = Crc32c.crc512 a hs (i + L2) hc2 s2 ∧
      st1.regs.x19 = Crc32c.fold512Lo a0 a1
        (b512w0 a hs (i + L3) hc3) (b512w1 a hs (i + L3) hc3)
        (b512w2 a hs (i + L3) hc3) (b512w3 a hs (i + L3) hc3)
        (b512w4 a hs (i + L3) hc3) (b512w5 a hs (i + L3) hc3)
        (b512w6 a hs (i + L3) hc3) ∧
      st1.regs.x20 = Crc32c.fold512Hi a0 a1
        (b512w0 a hs (i + L3) hc3) (b512w1 a hs (i + L3) hc3)
        (b512w2 a hs (i + L3) hc3) (b512w3 a hs (i + L3) hc3)
        (b512w4 a hs (i + L3) hc3) (b512w5 a hs (i + L3) hc3)
        (b512w7 a hs (i + L3) hc3) ∧
      st1.regs.x15 = s.regs.x15 ∧ st1.regs.x14 = s.regs.x14 ∧
      st1.regs.x12 = s.regs.x12 ∧ st1.regs.x11 = s.regs.x11 := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  rcases hinv with ⟨hx13_i, hx4_i, hx5_i, hx0_i, hx17_i, hx16_i, hx8_i, hx10_i,
    hv0_i, hv1_i, hv2_i, hv3_i, hv4_i, hv5_i, hv6_i, hv7_i⟩
  dsimp only at hc hro hpc hx9 hx6 hw22 hx23 hx24 hx21 hx3 hx19 hx20
  dsimp only at hx13_i hx4_i hx5_i hx0_i hx17_i hx16_i hx8_i hx10_i
  dsimp only at hv0_i hv1_i hv2_i hv3_i hv4_i hv5_i hv6_i hv7_i ⊢
  subst hpc
  have b3 := block512Reads_of_ro hro hs (i + L3) hc3
  have b4 := block512Reads_of_ro hro hs (i + L4) hc4
  have b5 := block512Reads_of_ro hro hs (i + L5) hc5
  have u4 : L4.toUInt64 + i.toUInt64 = (i + L4).toUInt64 :=
    usize_add_toUInt64_eq (by omega)
  have u5 : L5.toUInt64 + i.toUInt64 = (i + L5).toUInt64 :=
    usize_add_toUInt64_eq (by omega)
  have u64 : i.toUInt64 + 0x40 = (i + 64).toUInt64 := by
    have hus := usize_le_2pow64
    apply u64_ext
    rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64, h64]
    change (i.toNat + 64) % 2 ^ 64 = i.toNat + 64
    exact Nat.mod_eq_of_lt (by omega)
  apply Exists.intro
  apply And.intro
  · f6_step_with step_hwFold6Loop hc 91 hwFold6LoopInsn [hx19]
    f6_step_with step_hwFold6Loop hc 92 hwFold6LoopInsn [hx20]
    f6_step_with step_hwFold6Loop hc 93 hwFold6LoopInsn [hx6, b3.r6, b3.r7]
    f6_step_with step_hwFold6Loop hc 94 hwFold6LoopInsn [hv0_i]
    f6_step_with step_hwFold6Loop hc 95 hwFold6LoopInsn [hv1_i]
    f6_step_with step_hwFold6Loop hc 96 hwFold6LoopInsn [hx6, b3.r0, b3.r1]
    f6_step_with step_hwFold6Loop hc 97 hwFold6LoopInsn [hv2_i]
    f6_step_with step_hwFold6Loop hc 98 hwFold6LoopInsn [hx6, b3.r2, b3.r3]
    f6_step_with step_hwFold6Loop hc 99 hwFold6LoopInsn [hx6, b3.r4, b3.r5]
    f6_step_with step_hwFold6Loop hc 100 hwFold6LoopInsn [hx17_i, hx9, u4]
    f6_step_with step_hwFold6Loop hc 101 hwFold6LoopInsn [b4.vq6]
    f6_step step_hwFold6Loop hc 102 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 103 hwFold6LoopInsn [hx16_i, hx9, u5]
    f6_step_with step_hwFold6Loop hc 104 hwFold6LoopInsn [b5.vq6]
    f6_step_with step_hwFold6Loop hc 105 hwFold6LoopInsn [hv3_i]
    f6_step_with step_hwFold6Loop hc 106 hwFold6LoopInsn [hv4_i]
    f6_step_with step_hwFold6Loop hc 107 hwFold6LoopInsn [hv5_i]
    f6_step_with step_hwFold6Loop hc 108 hwFold6LoopInsn [hv6_i]
    f6_step_with step_hwFold6Loop hc 109 hwFold6LoopInsn [hv7_i]
    f6_step step_hwFold6Loop hc 110 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 111 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 112 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 113 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 114 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 115 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 116 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 117 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 118 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 119 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 120 hwFold6LoopInsn
    f6_step_with step_hwFold6Loop hc 121 hwFold6LoopInsn [hx9, u64]
    f6_step step_hwFold6Loop hc 122 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 123 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 124 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 125 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 126 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 127 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 128 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 129 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 130 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 131 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 132 hwFold6LoopInsn
    f6_step step_hwFold6Loop hc 133 hwFold6LoopInsn
    exact Arm64.run_zero _ _
  · dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3, getW_mk_r22] at hw22 ⊢
    rw [hw22, hx23, hx24, hx21, hx3, b512_crc512, fold512Lo_stream3, fold512Hi_stream3]
    exact ⟨rfl,
      ⟨hx13_i, hx4_i, hx5_i, hx0_i, rfl, rfl, hx8_i, hx10_i,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, toUInt32_toUInt64 _, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hwFold6Loop_body_s45 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {nextI stop ws L L2 L3 L4 L5 i : USize}
    (hc4 : (i + L4).toNat + 64 ≤ a.size)
    (hc5 : (i + L5).toNat + 64 ≤ a.size)
    {b0 b1 c0 c1 : UInt64}
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hinv : LoopConsts s base stop ws L L2 L3 L4 L5)
    (hpc : s.pc = Layout.hwFold6LoopBase + 536)
    (hx9 : s.regs.x9 = nextI.toUInt64)
    (hx7 : s.regs.x7 = base + (i + L4).toUInt64)
    (hx6 : s.regs.x6 = base + (i + L5).toUInt64)
    (hv17 : s.simd.v17 = V128.ofHalves (b512w6 a hs (i + L4) hc4) (b512w7 a hs (i + L4) hc4))
    (hv16 : s.simd.v16 = V128.ofHalves (b512w6 a hs (i + L5) hc5) (b512w7 a hs (i + L5) hc5))
    (hx15 : s.regs.x15 = b0)
    (hx14 : s.regs.x14 = b1)
    (hx12 : s.regs.x12 = c0)
    (hx11 : s.regs.x11 = c1) :
    let nb0 := Crc32c.fold512Lo b0 b1
      (b512w0 a hs (i + L4) hc4) (b512w1 a hs (i + L4) hc4)
      (b512w2 a hs (i + L4) hc4) (b512w3 a hs (i + L4) hc4)
      (b512w4 a hs (i + L4) hc4) (b512w5 a hs (i + L4) hc4)
      (b512w6 a hs (i + L4) hc4)
    let nb1 := Crc32c.fold512Hi b0 b1
      (b512w0 a hs (i + L4) hc4) (b512w1 a hs (i + L4) hc4)
      (b512w2 a hs (i + L4) hc4) (b512w3 a hs (i + L4) hc4)
      (b512w4 a hs (i + L4) hc4) (b512w5 a hs (i + L4) hc4)
      (b512w7 a hs (i + L4) hc4)
    let nc0 := Crc32c.fold512Lo c0 c1
      (b512w0 a hs (i + L5) hc5) (b512w1 a hs (i + L5) hc5)
      (b512w2 a hs (i + L5) hc5) (b512w3 a hs (i + L5) hc5)
      (b512w4 a hs (i + L5) hc5) (b512w5 a hs (i + L5) hc5)
      (b512w6 a hs (i + L5) hc5)
    let nc1 := Crc32c.fold512Hi c0 c1
      (b512w0 a hs (i + L5) hc5) (b512w1 a hs (i + L5) hc5)
      (b512w2 a hs (i + L5) hc5) (b512w3 a hs (i + L5) hc5)
      (b512w4 a hs (i + L5) hc5) (b512w5 a hs (i + L5) hc5)
      (b512w7 a hs (i + L5) hc5)
    ∃ k st1, Arm64.run code k s = some st1 ∧
      st1.pc = (if nextI < stop then Layout.hwFold6LoopBase + 220 else Layout.hwFold6LoopBase + 716) ∧
      LoopConsts st1 base stop ws L L2 L3 L4 L5 ∧
      KeepMeta s st1 ∧
      st1.regs.x9 = nextI.toUInt64 ∧
      st1.getW r1 = s.getW r1 ∧ st1.getW r2 = s.getW r2 ∧ st1.getW r3 = s.getW r3 ∧
      st1.regs.x19 = s.regs.x19 ∧ st1.regs.x20 = s.regs.x20 ∧
      st1.regs.x15 = nb0 ∧ st1.regs.x14 = nb1 ∧
      st1.regs.x12 = nc0 ∧ st1.regs.x11 = nc1 ∧
      st1.simd.v17 = V128.ofHalves nb0 nb1 ∧
      st1.simd.v16 = V128.ofHalves nc0 nc1 := by
  intro nb0 nb1 nc0 nc1
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  rcases hinv with ⟨hx13_i, hx4_i, hx5_i, hx0_i, hx17_i, hx16_i, hx8_i, hx10_i,
    hv0_i, hv1_i, hv2_i, hv3_i, hv4_i, hv5_i, hv6_i, hv7_i⟩
  dsimp only at hc hro hpc hx9 hx7 hx6 hv17 hv16 hx15 hx14 hx12 hx11
  dsimp only at hx13_i hx4_i hx5_i hx0_i hx17_i hx16_i hx8_i hx10_i
  dsimp only at hv0_i hv1_i hv2_i hv3_i hv4_i hv5_i hv6_i hv7_i ⊢
  subst hpc
  have b4 := block512Reads_of_ro hro hs (i + L4) hc4
  have b5 := block512Reads_of_ro hro hs (i + L5) hc5
  have hlt_iff : (nextI.toUInt64 < stop.toUInt64) ↔ (nextI < stop) := by
    change nextI.toUInt64.toNat < stop.toUInt64.toNat ↔ _
    rw [USize.toNat_toUInt64, USize.toNat_toUInt64, USize.lt_iff_toNat_lt]
  f6_step_ex_with step_hwFold6Loop hc 134 hwFold6LoopInsn [hx15]
  f6_step_ex_with step_hwFold6Loop hc 135 hwFold6LoopInsn [hv0_i]
  f6_step_ex_with step_hwFold6Loop hc 136 hwFold6LoopInsn [hx14]
  f6_step_ex_with step_hwFold6Loop hc 137 hwFold6LoopInsn [hv1_i]
  f6_step_ex_with step_hwFold6Loop hc 138 hwFold6LoopInsn [hx7, b4.r0, b4.r1]
  f6_step_ex_with step_hwFold6Loop hc 139 hwFold6LoopInsn [hv2_i]
  f6_step_ex_with step_hwFold6Loop hc 140 hwFold6LoopInsn [hv3_i]
  f6_step_ex_with step_hwFold6Loop hc 141 hwFold6LoopInsn [hx7, b4.r2, b4.r3]
  f6_step_ex_with step_hwFold6Loop hc 142 hwFold6LoopInsn [hv4_i]
  f6_step_ex_with step_hwFold6Loop hc 143 hwFold6LoopInsn [hv5_i]
  f6_step_ex_with step_hwFold6Loop hc 144 hwFold6LoopInsn [hx7, b4.r4, b4.r5]
  f6_step_ex_with step_hwFold6Loop hc 145 hwFold6LoopInsn [hv6_i]
  f6_step_ex_with step_hwFold6Loop hc 146 hwFold6LoopInsn [hv7_i]
  f6_step_ex_with step_hwFold6Loop hc 147 hwFold6LoopInsn [hx12]
  f6_step_ex_with step_hwFold6Loop hc 148 hwFold6LoopInsn [hv0_i]
  f6_step_ex_with step_hwFold6Loop hc 149 hwFold6LoopInsn [hx11]
  f6_step_ex_with step_hwFold6Loop hc 150 hwFold6LoopInsn [hv1_i]
  f6_step_ex_with step_hwFold6Loop hc 151 hwFold6LoopInsn [hx6, b5.r0, b5.r1]
  f6_step_ex_with step_hwFold6Loop hc 152 hwFold6LoopInsn [hv2_i]
  f6_step_ex_with step_hwFold6Loop hc 153 hwFold6LoopInsn [hv3_i]
  f6_step_ex_with step_hwFold6Loop hc 154 hwFold6LoopInsn [hx6, b5.r2, b5.r3]
  f6_step_ex_with step_hwFold6Loop hc 155 hwFold6LoopInsn [hv4_i]
  f6_step_ex_with step_hwFold6Loop hc 156 hwFold6LoopInsn [hv5_i]
  f6_step_ex_with step_hwFold6Loop hc 157 hwFold6LoopInsn [hx6, b5.r4, b5.r5]
  f6_step_ex_with step_hwFold6Loop hc 158 hwFold6LoopInsn [hv6_i]
  f6_step_ex_with step_hwFold6Loop hc 159 hwFold6LoopInsn [hv7_i]
  f6_step_ex_with step_hwFold6Loop hc 160 hwFold6LoopInsn [hv17]
  f6_step_ex step_hwFold6Loop hc 161 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 162 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 163 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 164 hwFold6LoopInsn [hv16]
  f6_step_ex step_hwFold6Loop hc 165 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 166 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 167 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 168 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 169 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 170 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 171 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 172 hwFold6LoopInsn [hx9, hx8_i]
  by_cases hlt : nextI < stop
  · have hltu : nextI.toUInt64 < stop.toUInt64 := hlt_iff.mpr hlt
    have hif : (if nextI < stop then Layout.hwFold6LoopBase + 220 else Layout.hwFold6LoopBase + 716) =
        Layout.hwFold6LoopBase + 220 := by simp [hlt]
    f6_step_ex_with step_hwFold6Loop hc 173 hwFold6LoopInsn [hltu]
    refine ⟨0, _, Arm64.run_zero _ _, ?_⟩
    rw [hif]
    dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3]
    exact ⟨rfl,
      ⟨hx13_i, hx4_i, hx5_i, hx0_i, hx17_i, hx16_i, rfl, hx10_i,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hnltu : ¬ (nextI.toUInt64 < stop.toUInt64) := fun h => hlt (hlt_iff.mp h)
    have hif : (if nextI < stop then Layout.hwFold6LoopBase + 220 else Layout.hwFold6LoopBase + 716) =
        Layout.hwFold6LoopBase + 716 := by simp [hlt]
    f6_step_ex_with step_hwFold6Loop hc 173 hwFold6LoopInsn [hnltu]
    f6_step_ex step_hwFold6Loop hc 174 hwFold6LoopInsn
    refine ⟨0, _, Arm64.run_zero _ _, ?_⟩
    rw [hif]
    dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3]
    exact ⟨rfl,
      ⟨hx13_i, hx4_i, hx5_i, hx0_i, hx17_i, hx16_i, rfl, hx10_i,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hwFold6Loop_loop {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {stop ws L L2 L3 L4 L5 : USize}
    (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat) (hL5 : L5.toNat = 5 * L.toNat)
    (hL : stop.toNat + 5 * L.toNat ≤ a.size) :
    ∀ (rem : Nat) (s orig : Arm64.ArmState) (i : USize)
      (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 64 = 0)
      (_hrem : stop.toNat - i.toNat = rem) (_hlt : i < stop)
      (s0 s1 s2 : UInt32) (a0 a1 b0 b1 c0 c1 : UInt64),
      CodeLoaded code s.mem Layout →
      GlobalsLoaded s.mem Layout →
      s.mem.hasROBytes base a →
      LoopConsts s base stop ws L L2 L3 L4 L5 →
      s.pc = Layout.hwFold6LoopBase + 220 →
      s.sp = orig.sp - 0x60 →
      SavedFrame6Loop s.mem (orig.sp - 0x60) orig →
      s.regs.x9 = i.toUInt64 →
      s.getW r1 = s0 → s.getW r2 = s1 → s.getW r3 = s2 →
      s.regs.x19 = a0 → s.regs.x20 = a1 →
      s.regs.x15 = b0 → s.regs.x14 = b1 →
      s.regs.x12 = c0 → s.regs.x11 = c1 →
      s.regs.x29 = orig.regs.x29 → s.regs.x30 = orig.regs.x30 →
      s.getD r10 = orig.getD r10 → s.getD r11 = orig.getD r11 →
      s.getD r12 = orig.getD r12 → s.getD r13 = orig.getD r13 →
      s.getD r14 = orig.getD r14 → s.getD r15 = orig.getD r15 →
      ∃ steps s', Arm64.run code steps s = some s' ∧
        s'.pc = orig.regs.x30 ∧
        s'.getW r0 = Crc32c.hwFold6Loop a hs i stop ws L L2 L3 L4 L5
          hi hal hL2 hL3 hL4 hL5 hL s0 s1 s2 a0 a1 b0 b1 c0 c1 ∧
        s'.mem = s.mem ∧
        CalleeSaved orig s' := by
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s orig i hi hal hrem hlt s0 s1 s2 a0 a1 b0 b1 c0 c1
      hc hg hro hinv hpc hsp hframe hx9 hw1 hw2 hw3 hx19 hx20 hx15 hx14 hx12 hx11
      hx29 hx30 hd10 hd11 hd12 hd13 hd14 hd15
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have h64le : i.toNat + 64 ≤ stop.toNat := by
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    have h64 : (i + 64).toNat = i.toNat + 64 := Crc32c.usize_add_toNat i 64 (by omega)
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
    have hc0 : i.toNat + 64 ≤ a.size := by omega
    have hc1 : (i + L).toNat + 64 ≤ a.size := by omega
    have hc2 : (i + L2).toNat + 64 ≤ a.size := by omega
    have hc3 : (i + L3).toNat + 64 ≤ a.size := by omega
    have hc4 : (i + L4).toNat + 64 ≤ a.size := by omega
    have hc5 : (i + L5).toNat + 64 ≤ a.size := by omega
    rcases hwFold6Loop_body_crc hs hi1 hi2 hi3 hL2 hL3 hc0 hc1 hc2
        hc hro hinv hpc hx9 hw1 hw2 hw3 with
      ⟨s1st, hr1, hpc1, hinv1, hkm1, hx9_1, hx6_1, hw1_1, hw2_1, hw22_1,
       hx23_1, hx24_1, hx21_1, hx3_1, hx19_1, hx20_1, hx15_1, hx14_1, hx12_1, hx11_1⟩
    rcases hwFold6Loop_body_s3 hs h64 hi4 hi5 hL4 hL5 hc2 hc3 hc4 hc5
        (hkm1.mem ▸ hc) (hkm1.mem ▸ hro) hinv1 hpc1 hx9_1 hx6_1 hw22_1
        hx23_1 hx24_1 hx21_1 hx3_1 (hx19_1.trans hx19) (hx20_1.trans hx20) with
      ⟨s2st, hr2, hpc2, hinv2, hkm2, hx9_2, hx7_2, hx6_2, hv17_2, hv16_2,
       hw1_2, hw2_2, hw3_2, hx19_2, hx20_2, hx15_2, hx14_2, hx12_2, hx11_2⟩
    have hkm12 := hkm1.trans hkm2
    rcases hwFold6Loop_body_s45 hs hc4 hc5
        (hkm12.mem ▸ hc) (hkm12.mem ▸ hro) hinv2 hpc2 hx9_2 hx7_2 hx6_2 hv17_2 hv16_2
        (hx15_2.trans (hx15_1.trans hx15)) (hx14_2.trans (hx14_1.trans hx14))
        (hx12_2.trans (hx12_1.trans hx12)) (hx11_2.trans (hx11_1.trans hx11)) with
      ⟨k3, s3st, hr3, hpc3, hinv3, hkm3, hx9_3, hw1_3, hw2_3, hw3_3,
       hx19_3, hx20_3, hx15_3, hx14_3, hx12_3, hx11_3, hv17_3, hv16_3⟩
    have hkm := hkm12.trans hkm3
    refine run_bind_exists hr1 (run_bind_exists hr2 (run_bind_exists hr3 ?_))
    have hle' : (i + 64).toNat ≤ stop.toNat := by omega
    have hal' : (stop.toNat - (i + 64).toNat) % 64 = 0 := by omega
    let ns0 := Crc32c.crc512 a hs i hc0 s0
    let ns1 := Crc32c.crc512 a hs (i + L) hc1 s1
    let ns2 := Crc32c.crc512 a hs (i + L2) hc2 s2
    let na0 := Crc32c.fold512Lo a0 a1
      (b512w0 a hs (i + L3) hc3) (b512w1 a hs (i + L3) hc3) (b512w2 a hs (i + L3) hc3)
      (b512w3 a hs (i + L3) hc3) (b512w4 a hs (i + L3) hc3) (b512w5 a hs (i + L3) hc3)
      (b512w6 a hs (i + L3) hc3)
    let na1 := Crc32c.fold512Hi a0 a1
      (b512w0 a hs (i + L3) hc3) (b512w1 a hs (i + L3) hc3) (b512w2 a hs (i + L3) hc3)
      (b512w3 a hs (i + L3) hc3) (b512w4 a hs (i + L3) hc3) (b512w5 a hs (i + L3) hc3)
      (b512w7 a hs (i + L3) hc3)
    let nb0 := Crc32c.fold512Lo b0 b1
      (b512w0 a hs (i + L4) hc4) (b512w1 a hs (i + L4) hc4) (b512w2 a hs (i + L4) hc4)
      (b512w3 a hs (i + L4) hc4) (b512w4 a hs (i + L4) hc4) (b512w5 a hs (i + L4) hc4)
      (b512w6 a hs (i + L4) hc4)
    let nb1 := Crc32c.fold512Hi b0 b1
      (b512w0 a hs (i + L4) hc4) (b512w1 a hs (i + L4) hc4) (b512w2 a hs (i + L4) hc4)
      (b512w3 a hs (i + L4) hc4) (b512w4 a hs (i + L4) hc4) (b512w5 a hs (i + L4) hc4)
      (b512w7 a hs (i + L4) hc4)
    let nc0 := Crc32c.fold512Lo c0 c1
      (b512w0 a hs (i + L5) hc5) (b512w1 a hs (i + L5) hc5) (b512w2 a hs (i + L5) hc5)
      (b512w3 a hs (i + L5) hc5) (b512w4 a hs (i + L5) hc5) (b512w5 a hs (i + L5) hc5)
      (b512w6 a hs (i + L5) hc5)
    let nc1 := Crc32c.fold512Hi c0 c1
      (b512w0 a hs (i + L5) hc5) (b512w1 a hs (i + L5) hc5) (b512w2 a hs (i + L5) hc5)
      (b512w3 a hs (i + L5) hc5) (b512w4 a hs (i + L5) hc5) (b512w5 a hs (i + L5) hc5)
      (b512w7 a hs (i + L5) hc5)
    have hstep_eq : Crc32c.hwFold6Loop a hs i stop ws L L2 L3 L4 L5 hi hal hL2 hL3 hL4 hL5 hL
        s0 s1 s2 a0 a1 b0 b1 c0 c1 =
        Crc32c.hwFold6Loop a hs (i + 64) stop ws L L2 L3 L4 L5 hle' hal' hL2 hL3 hL4 hL5 hL
          ns0 ns1 ns2 na0 na1 nb0 nb1 nc0 nc1 := by
      conv_lhs => rw [Crc32c.hwFold6Loop]
      simp only [hlt, ↓reduceDIte, withBlock512_eq_b512]; rfl
    rw [hstep_eq]
    by_cases hnext : i + 64 < stop
    · simp only [hnext, ↓reduceIte] at hpc3
      rcases ih (stop.toNat - (i + 64).toNat) (by omega) s3st orig (i + 64)
          hle' hal' rfl hnext
          ns0 ns1 ns2 na0 na1 nb0 nb1 nc0 nc1
          (hkm.mem ▸ hc) (hkm.mem ▸ hg) (hkm.mem ▸ hro) hinv3 hpc3
          (hkm.sp.trans hsp) (hkm.mem ▸ hframe) hx9_3
          (hw1_3.trans (hw1_2.trans hw1_1))
          (hw2_3.trans (hw2_2.trans hw2_1))
          (hw3_3.trans hw3_2)
          (hx19_3.trans hx19_2) (hx20_3.trans hx20_2)
          hx15_3 hx14_3 hx12_3 hx11_3
          (hkm.x29.trans hx29) (hkm.x30.trans hx30)
          (hkm.d10.trans hd10) (hkm.d11.trans hd11)
          (hkm.d12.trans hd12) (hkm.d13.trans hd13)
          (hkm.d14.trans hd14) (hkm.d15.trans hd15) with
        ⟨k4, s', hr4, hpc', hr0', hmem', hcs'⟩
      exact ⟨k4, s', hr4, hpc', hr0', hmem'.trans hkm.mem, hcs'⟩
    · simp only [hnext, ↓reduceIte] at hpc3
      have hstop_eq : Crc32c.hwFold6Loop a hs (i + 64) stop ws L L2 L3 L4 L5 hle' hal'
          hL2 hL3 hL4 hL5 hL
          ns0 ns1 ns2 na0 na1 nb0 nb1 nc0 nc1 =
          Crc32c.combine6 ws ns0 ns1 ns2
            (Crc32c.finish128 na0 na1) (Crc32c.finish128 nb0 nb1) (Crc32c.finish128 nc0 nc1) := by
        conv_lhs => rw [Crc32c.hwFold6Loop]
        simp only [hnext, ↓reduceDIte]
      rw [hstop_eq]
      rcases hwFold6Loop_epilogue (hkm.mem ▸ hc) (hkm.mem ▸ hg) hpc3
          (hkm.sp.trans hsp) (hkm.mem ▸ hframe) hinv3.x10
          (hw1_3.trans (hw1_2.trans hw1_1))
          (hw2_3.trans (hw2_2.trans hw2_1))
          (hw3_3.trans hw3_2)
          (hx19_3.trans hx19_2) (hx20_3.trans hx20_2)
          hv17_3 hv16_3
          (hkm.x29.trans hx29) (hkm.x30.trans hx30)
          (hkm.d10.trans hd10) (hkm.d11.trans hd11)
          (hkm.d12.trans hd12) (hkm.d13.trans hd13)
          (hkm.d14.trans hd14) (hkm.d15.trans hd15) with
        ⟨k4, s', hr4, hpc', hr0', hmem', hcs'⟩
      exact ⟨k4, s', hr4, hpc', hr0', hmem'.trans hkm.mem, hcs'⟩

private theorem hwFold6Loop_setup {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr base : UInt64}
    {stop ws L L2 L3 L4 L5 : USize}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hpc : s.pc = Layout.hwFold6LoopBase + 64)
    (hbase : objPtr + 0x18 = base)
    (hx0 : s.regs.x0 = objPtr)
    (hx4 : s.regs.x4 = L.toUInt64)
    (hx5 : s.regs.x5 = L2.toUInt64)
    (hx6 : s.regs.x6 = L3.toUInt64)
    (hx7 : s.regs.x7 = L4.toUInt64)
    (hx8 : s.regs.x8 = stop.toUInt64)
    (hx10 : s.regs.x10 = ws.toUInt64)
    (hL5_stk : s.mem.readU64LE (s.sp + 0x60) = some L5.toUInt64) :
    ∃ k st1, Arm64.run code k s = some st1 ∧
      st1.pc = Layout.hwFold6LoopBase + 220 ∧
      LoopConsts st1 base stop ws L L2 L3 L4 L5 ∧
      KeepMeta s st1 ∧
      st1.regs.x9 = s.regs.x9 ∧
      st1.getW r1 = s.getW r1 ∧ st1.getW r2 = s.getW r2 ∧ st1.getW r3 = s.getW r3 ∧
      st1.regs.x19 = s.regs.x19 ∧ st1.regs.x20 = s.regs.x20 ∧
      st1.regs.x15 = s.regs.x15 ∧ st1.regs.x14 = s.regs.x14 ∧
      st1.regs.x12 = s.regs.x12 ∧ st1.regs.x11 = s.regs.x11 := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hx0 hx4 hx5 hx6 hx7 hx8 hx10 hL5_stk ⊢
  subst hpc
  have g17 := hc.hwFold6Loop.2.2 { idx := 17, rd := r17, target := .gKFold512_1 } (by decide)
  have g21 := hc.hwFold6Loop.2.2 { idx := 21, rd := r17, target := .gKFold512_2 } (by decide)
  have g23 := hc.hwFold6Loop.2.2 { idx := 23, rd := r0, target := .gKFold384_1 } (by decide)
  have g27 := hc.hwFold6Loop.2.2 { idx := 27, rd := r17, target := .gKFold384_2 } (by decide)
  have g29 := hc.hwFold6Loop.2.2 { idx := 29, rd := r0, target := .gKFold256_1 } (by decide)
  have g33 := hc.hwFold6Loop.2.2 { idx := 33, rd := r17, target := .gKFold256_2 } (by decide)
  have g35 := hc.hwFold6Loop.2.2 { idx := 35, rd := r0, target := .gKFold128_1 } (by decide)
  have g39 := hc.hwFold6Loop.2.2 { idx := 39, rd := r28, target := .gKFold128_2 } (by decide)
  have rk512_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold512_1
  have rk512_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold512_2
  have rk384_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold384_1
  have rk384_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold384_2
  have rk256_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold256_1
  have rk256_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold256_2
  have rk128_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold128_1
  have rk128_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold128_2
  f6_step_ex_with step_hwFold6Loop hc 16 hwFold6LoopInsn [hL5_stk]
  f6_gotPair g17
  f6_step_ex_with step_hwFold6Loop hc 19 hwFold6LoopInsn [hx0, hbase]
  f6_step_ex_with step_hwFold6Loop hc 20 hwFold6LoopInsn [rk512_1]
  f6_gotPair g21
  f6_gotPair g23
  f6_step_ex_with step_hwFold6Loop hc 25 hwFold6LoopInsn [rk512_2]
  f6_step_ex_with step_hwFold6Loop hc 26 hwFold6LoopInsn [rk384_1]
  f6_gotPair g27
  f6_gotPair g29
  f6_step_ex_with step_hwFold6Loop hc 31 hwFold6LoopInsn [rk384_2]
  f6_step_ex_with step_hwFold6Loop hc 32 hwFold6LoopInsn [rk256_1]
  f6_gotPair g33
  f6_gotPair g35
  f6_step_ex_with step_hwFold6Loop hc 37 hwFold6LoopInsn [rk256_2]
  f6_step_ex_with step_hwFold6Loop hc 38 hwFold6LoopInsn [rk128_1]
  f6_gotPair g39
  f6_step_ex step_hwFold6Loop hc 41 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 42 hwFold6LoopInsn [hx7]
  f6_step_ex_with step_hwFold6Loop hc 43 hwFold6LoopInsn [hx6]
  f6_step_ex_with step_hwFold6Loop hc 44 hwFold6LoopInsn [hx5]
  f6_step_ex_with step_hwFold6Loop hc 45 hwFold6LoopInsn [hx4]
  f6_step_ex step_hwFold6Loop hc 46 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 47 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 48 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 49 hwFold6LoopInsn
  f6_step_ex_with step_hwFold6Loop hc 50 hwFold6LoopInsn [rk128_2]
  f6_step_ex step_hwFold6Loop hc 51 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 52 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 53 hwFold6LoopInsn
  f6_step_ex step_hwFold6Loop hc 54 hwFold6LoopInsn
  exact ⟨0, _, Arm64.run_zero _ _, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hx8, hx10, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Machine-code specification of `_lp_leancrc32c_Crc32c_hwFold6Loop___redArg`:
executes from `Layout.hwFold6LoopBase` (reading register arguments `X0..X7` and
Darwin AAPCS64 stack arguments at `[s.sp, s.sp + 0x48)`), tail-calling `combine6`
and returning to `s.regs.x30` with `W0 = Crc32c.hwFold6Loop ...`, touching only
stack frame `[s.sp - 0x60, s.sp)` and preserving all AAPCS64 callee-saved registers. -/
theorem hwFold6Loop_mc_spec {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {i stop ws L L2 L3 L4 L5 : USize}
    (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 64 = 0)
    (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat) (hL5 : L5.toNat = 5 * L.toNat)
    (hL : stop.toNat + 5 * L.toNat ≤ a.size)
    {s0 s1 s2 : UInt32} {a0 a1 b0 b1 c0 c1 : UInt64}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.hwFold6LoopBase)
    (hsp_lo : 0x60 ≤ s.sp.toNat)
    (hsp_hi : s.sp.toNat + 0x48 ≤ UInt64.size)
    (hrw : s.mem.isRWRange (s.sp - 0x60) 0x60)
    (hx0 : s.regs.x0 = objPtr)
    (hx1 : s.regs.x1 = i.toUInt64)
    (hx2 : s.regs.x2 = stop.toUInt64)
    (hx3 : s.regs.x3 = ws.toUInt64)
    (hx4 : s.regs.x4 = L.toUInt64)
    (hx5 : s.regs.x5 = L2.toUInt64)
    (hx6 : s.regs.x6 = L3.toUInt64)
    (hx7 : s.regs.x7 = L4.toUInt64)
    (hstk_L5 : s.mem.readU64LE s.sp = some L5.toUInt64)
    (hstk_s0 : s.mem.readU32LE (s.sp + 0x08) = some s0)
    (hstk_s1 : s.mem.readU32LE (s.sp + 0x0c) = some s1)
    (hstk_s2 : s.mem.readU32LE (s.sp + 0x10) = some s2)
    (hstk_a0 : s.mem.readU64LE (s.sp + 0x18) = some a0)
    (hstk_a1 : s.mem.readU64LE (s.sp + 0x20) = some a1)
    (hstk_b0 : s.mem.readU64LE (s.sp + 0x28) = some b0)
    (hstk_b1 : s.mem.readU64LE (s.sp + 0x30) = some b1)
    (hstk_c0 : s.mem.readU64LE (s.sp + 0x38) = some c0)
    (hstk_c1 : s.mem.readU64LE (s.sp + 0x40) = some c1) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.hwFold6Loop a hs i stop ws L L2 L3 L4 L5
        hi hal hL2 hL3 hL4 hL5 hL s0 s1 s2 a0 a1 b0 b1 c0 c1 ∧
      StackDelta code Layout s.mem s'.mem (s.sp - 0x60) 0x60 ∧
      CalleeSaved s s' := by
  obtain ⟨base, hbase⟩ : ∃ base : UInt64, objPtr + 0x18 = base := ⟨objPtr + 0x18, rfl⟩
  rw [hbase] at hro
  rcases hwFold6Loop_prologue hc hg hpc hsp_lo hrw with ⟨mFrame, hpro, hdelta, hsaved⟩
  have hlo_nat : (s.sp - 0x60).toNat + 0x60 = s.sp.toNat := by
    have : (0x60 : UInt64).toNat = 0x60 := rfl
    have hle : (0x60 : UInt64) ≤ s.sp := by change 0x60 ≤ s.sp.toNat; omega
    rw [UInt64.toNat_sub_of_le _ _ hle]; omega
  have r64_stk (off : UInt64) (hoff : off.toNat + 8 ≤ 0x48 := by decide) :
      mFrame.readU64LE (s.sp + off) = s.mem.readU64LE (s.sp + off) := by
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (s.sp + off).toNat = s.sp.toNat + off.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hdelta.outside.readU64LE (s.sp + off) (by omega) (by omega)
  have r32_stk (off : UInt64) (hoff : off.toNat + 4 ≤ 0x48 := by decide) :
      mFrame.readU32LE (s.sp + off) = s.mem.readU32LE (s.sp + off) := by
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (s.sp + off).toNat = s.sp.toNat + off.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hdelta.outside.readU32LE (s.sp + off) (by omega) (by omega)
  have m_L5 : mFrame.readU64LE ((s.sp - 0x60) + 0x60) = some L5.toUInt64 := by
    rw [u64_sub_add_cancel, ← UInt64.add_zero s.sp, r64_stk 0, UInt64.add_zero, hstk_L5]
  have m_s0 : mFrame.readU32LE ((s.sp - 0x60) + 0x68) = some s0 := by
    rw [sub_0x60_add s.sp 0x68 0x08, r32_stk 0x08, hstk_s0]
  have m_s1 : mFrame.readU32LE ((s.sp - 0x60) + 0x6c) = some s1 := by
    rw [sub_0x60_add s.sp 0x6c 0x0c, r32_stk 0x0c, hstk_s1]
  have m_s2 : mFrame.readU32LE ((s.sp - 0x60) + (0x6c + 4)) = some s2 := by
    rw [sub_0x60_add s.sp (0x6c + 4) 0x10, r32_stk 0x10, hstk_s2]
  have m_a0 : mFrame.readU64LE ((s.sp - 0x60) + 0x78) = some a0 := by
    rw [sub_0x60_add s.sp 0x78 0x18, r64_stk 0x18, hstk_a0]
  have m_a1 : mFrame.readU64LE ((s.sp - 0x60) + (0x78 + 8)) = some a1 := by
    rw [sub_0x60_add s.sp (0x78 + 8) 0x20, r64_stk 0x20, hstk_a1]
  have m_b0 : mFrame.readU64LE ((s.sp - 0x60) + 0x88) = some b0 := by
    rw [sub_0x60_add s.sp 0x88 0x28, r64_stk 0x28, hstk_b0]
  have m_b1 : mFrame.readU64LE ((s.sp - 0x60) + (0x88 + 8)) = some b1 := by
    rw [sub_0x60_add s.sp (0x88 + 8) 0x30, r64_stk 0x30, hstk_b1]
  have m_c0 : mFrame.readU64LE ((s.sp - 0x60) + 0x98) = some c0 := by
    rw [sub_0x60_add s.sp 0x98 0x38, r64_stk 0x38, hstk_c0]
  have m_c1 : mFrame.readU64LE ((s.sp - 0x60) + (0x98 + 8)) = some c1 := by
    rw [sub_0x60_add s.sp (0x98 + 8) 0x40, r64_stk 0x40, hstk_c1]
  have hcF := hdelta.codeLoaded
  have hgF := hdelta.globalsLoaded
  have hroF := hdelta.hasROBytes hro
  suffices hbody : ∃ k2 s', Arm64.run code k2 { s with
        sp := s.sp - 0x60, pc := Layout.hwFold6LoopBase + 24, mem := mFrame } = some s' ∧
      (s'.pc = s.regs.x30 ∧
       s'.getW r0 = Crc32c.hwFold6Loop a hs i stop ws L L2 L3 L4 L5
         hi hal hL2 hL3 hL4 hL5 hL s0 s1 s2 a0 a1 b0 b1 c0 c1 ∧
       s'.mem = mFrame ∧
       CalleeSaved s s') by
    rcases run_bind_exists hpro hbody with ⟨ktot, s', hrtot, hpctot, hr0tot, hmemtot, hcstot⟩
    exact ⟨ktot, s', hrtot, hpctot, hr0tot, hmemtot ▸ hdelta, hcstot⟩
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 m_L5 m_s0 m_s1 m_s2 m_a0 m_a1 m_b0 m_b1 m_c0 m_c1 hsaved ⊢
  f6_step_ex_with step_hwFold6Loop hcF 6 hwFold6LoopInsn [hx3]
  f6_step_ex_with step_hwFold6Loop hcF 7 hwFold6LoopInsn [hx2]
  f6_step_ex_with step_hwFold6Loop hcF 8 hwFold6LoopInsn [hx1]
  f6_step_ex_with step_hwFold6Loop hcF 9 hwFold6LoopInsn [m_c0, m_c1]
  f6_step_ex_with step_hwFold6Loop hcF 10 hwFold6LoopInsn [m_b0, m_b1]
  f6_step_ex_with step_hwFold6Loop hcF 11 hwFold6LoopInsn [m_a0, m_a1]
  f6_step_ex_with step_hwFold6Loop hcF 12 hwFold6LoopInsn [m_s1, m_s2]
  f6_step_ex_with step_hwFold6Loop hcF 13 hwFold6LoopInsn [m_s0]
  f6_step_ex step_hwFold6Loop hcF 14 hwFold6LoopInsn
  have hge_iff : (stop.toUInt64 ≤ i.toUInt64) ↔ ¬ (i < stop) := by
    change stop.toUInt64.toNat ≤ i.toUInt64.toNat ↔ _
    rw [USize.toNat_toUInt64, USize.toNat_toUInt64, USize.lt_iff_toNat_lt]
    omega
  by_cases hlt : i < stop
  · have hnge : ¬ (stop.toUInt64 ≤ i.toUInt64) := fun h => (hge_iff.mp h) hlt
    f6_step_ex_with step_hwFold6Loop hcF 15 hwFold6LoopInsn [hnge]
    apply run_bind_of_setup
    · exact hwFold6Loop_setup hcF hgF rfl hbase hx0 hx4 hx5 hx6 hx7 rfl rfl m_L5
    · rintro ss ⟨hpcs, hinvs, hkms, hx9s, hw1s, hw2s, hw3s,
        hx19s, hx20s, hx15s, hx14s, hx12s, hx11s⟩
      have hmem_ss : ss.mem = mFrame := hkms.mem
      rcases hwFold6Loop_loop hs hL2 hL3 hL4 hL5 hL
          (stop.toNat - i.toNat) ss { regs, sp, simd, nzcv, pc, mem } i hi hal rfl hlt
          s0 s1 s2 a0 a1 b0 b1 c0 c1
          (hmem_ss ▸ hcF) (hmem_ss ▸ hgF) (hmem_ss ▸ hroF) hinvs hpcs
          hkms.sp (hmem_ss ▸ hsaved) hx9s
          (hw1s.trans (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r1]; exact toUInt32_toUInt64 _))
          (hw2s.trans (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r2]; exact toUInt32_toUInt64 _))
          (hw3s.trans (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r3]; exact toUInt32_toUInt64 _))
          hx19s hx20s hx15s hx14s hx12s hx11s
          hkms.x29 hkms.x30 hkms.d10 hkms.d11 hkms.d12 hkms.d13 hkms.d14 hkms.d15 with
        ⟨kl, s', hrl, hpcl, hr0l, hmeml, hcsl⟩
      exact ⟨kl, s', hrl, hpcl, hr0l, hmeml.trans hmem_ss, hcsl⟩
  · have hge : stop.toUInt64 ≤ i.toUInt64 := hge_iff.mpr hlt
    f6_step_ex_with step_hwFold6Loop hcF 15 hwFold6LoopInsn [hge]
    f6_step_ex step_hwFold6Loop hcF 175 hwFold6LoopInsn
    f6_step_ex step_hwFold6Loop hcF 176 hwFold6LoopInsn
    f6_step_ex step_hwFold6Loop hcF 177 hwFold6LoopInsn
    f6_step_ex step_hwFold6Loop hcF 178 hwFold6LoopInsn
    have hstop0 : Crc32c.hwFold6Loop a hs i stop ws L L2 L3 L4 L5 hi hal hL2 hL3 hL4 hL5 hL
        s0 s1 s2 a0 a1 b0 b1 c0 c1 =
        Crc32c.combine6 ws s0 s1 s2
          (Crc32c.finish128 a0 a1) (Crc32c.finish128 b0 b1) (Crc32c.finish128 c0 c1) := by
      conv_lhs => rw [Crc32c.hwFold6Loop]
      simp only [hlt, ↓reduceDIte]
    rw [hstop0]
    apply let_cur_state
    intro st
    exact hwFold6Loop_epilogue (s := st) (orig := { regs, sp, simd, nzcv, pc, mem })
      hcF hgF rfl rfl hsaved rfl
      (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r1]; exact toUInt32_toUInt64 _)
      (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r2]; exact toUInt32_toUInt64 _)
      (by dsimp only [Arm64.ArmState.getW, Arm64.RegFile.get, r3]; exact toUInt32_toUInt64 _)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-! ### Section 5: `hwFold6` machine-code verification (`186` instructions) -/

private theorem usize_add_toUInt64_eq' {x y : USize} (h : (x + y).toNat = x.toNat + y.toNat) :
    x.toUInt64 + y.toUInt64 = (x + y).toUInt64 := by
  rw [UInt64.add_comm]
  exact usize_add_toUInt64_eq h

private theorem sp_sub_0xa0_sub_0x60 (sp : UInt64) : (sp - 0xa0) - 0x60 = sp - 0x100 := by
  rw [← UInt64.toBitVec_inj]
  simp only [UInt64.toBitVec_sub]
  rw [BitVec.sub_sub]
  rfl

private structure SavedFrame6 (m : Arm64.Mem) (sp0 : UInt64) (orig : Arm64.ArmState) : Prop where
  sx26 : m.readU64LE (sp0 + 0x50) = some orig.regs.x26
  sx25 : m.readU64LE (sp0 + (0x50 + 8)) = some orig.regs.x25
  sx24 : m.readU64LE (sp0 + 0x60) = some orig.regs.x24
  sx23 : m.readU64LE (sp0 + (0x60 + 8)) = some orig.regs.x23
  sx22 : m.readU64LE (sp0 + 0x70) = some orig.regs.x22
  sx21 : m.readU64LE (sp0 + (0x70 + 8)) = some orig.regs.x21
  sx20 : m.readU64LE (sp0 + 0x80) = some orig.regs.x20
  sx19 : m.readU64LE (sp0 + (0x80 + 8)) = some orig.regs.x19
  sx29 : m.readU64LE (sp0 + 0x90) = some orig.regs.x29
  sx30 : m.readU64LE (sp0 + (0x90 + 8)) = some orig.regs.x30

private theorem SavedFrame6.of_memOutsideEq {m m' : Arm64.Mem} {sp0 subLo : UInt64} {subLen : Nat}
    {orig : Arm64.ArmState}
    (hsf : SavedFrame6 m sp0 orig)
    (hout : MemOutsideEq m m' subLo subLen)
    (hb : sp0.toNat + 0xa0 ≤ UInt64.size)
    (hdisj : subLo.toNat + subLen ≤ sp0.toNat + 0x50) :
    SavedFrame6 m' sp0 orig := by
  have r64 (off : UInt64) (hoff : decide (0x50 ≤ off.toNat ∧ off.toNat + 8 ≤ 0xa0) = true := by decide) :
      m'.readU64LE (sp0 + off) = m.readU64LE (sp0 + off) := by
    have hp := of_decide_eq_true hoff
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (sp0 + off).toNat = sp0.toNat + off.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hout.readU64LE (sp0 + off) (by omega) (by omega)
  exact ⟨(r64 0x50).trans hsf.sx26, (r64 (0x50 + 8)).trans hsf.sx25,
    (r64 0x60).trans hsf.sx24, (r64 (0x60 + 8)).trans hsf.sx23,
    (r64 0x70).trans hsf.sx22, (r64 (0x70 + 8)).trans hsf.sx21,
    (r64 0x80).trans hsf.sx20, (r64 (0x80 + 8)).trans hsf.sx19,
    (r64 0x90).trans hsf.sx29, (r64 (0x90 + 8)).trans hsf.sx30⟩

private structure KeepMeta6 (s s' : Arm64.ArmState) : Prop where
  sp  : s'.sp = s.sp
  mem : s'.mem = s.mem
  x27 : s'.regs.x27 = s.regs.x27
  x28 : s'.regs.x28 = s.regs.x28
  d8  : s'.getD r8 = s.getD r8
  d9  : s'.getD r9 = s.getD r9
  d10 : s'.getD r10 = s.getD r10
  d11 : s'.getD r11 = s.getD r11
  d12 : s'.getD r12 = s.getD r12
  d13 : s'.getD r13 = s.getD r13
  d14 : s'.getD r14 = s.getD r14
  d15 : s'.getD r15 = s.getD r15

private theorem KeepMeta6.trans {s1 s2 s3 : Arm64.ArmState}
    (h12 : KeepMeta6 s1 s2) (h23 : KeepMeta6 s2 s3) : KeepMeta6 s1 s3 :=
  ⟨h23.sp.trans h12.sp, h23.mem.trans h12.mem, h23.x27.trans h12.x27, h23.x28.trans h12.x28,
   h23.d8.trans h12.d8, h23.d9.trans h12.d9, h23.d10.trans h12.d10, h23.d11.trans h12.d11,
   h23.d12.trans h12.d12, h23.d13.trans h12.d13, h23.d14.trans h12.d14, h23.d15.trans h12.d15⟩

private theorem hwFold6_prologue {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hpc : s.pc = Layout.hwFold6Base)
    (hrw : s.mem.isRWRange (s.sp - 0xa0) 0xa0) :
    ∃ mPro : Arm64.Mem,
      Arm64.run code 6 s = some { s with
        sp := s.sp - 0xa0
        pc := Layout.hwFold6Base + 24
        mem := mPro } ∧
      StackDelta code Layout s.mem mPro (s.sp - 0xa0) 0xa0 ∧
      SavedFrame6 mPro (s.sp - 0xa0) s := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hpc hrw ⊢
  subst hpc
  have hb : (sp - 0xa0).toNat + 0xa0 ≤ UInt64.size := hrw.1
  have d0 := StackDelta.refl hrw hc hg
  have w0 := writeU64LE_sp_off d0.rwRange 0x50 regs.x26
  have d1 := d0.step64 0x50 regs.x26
  have w1 := writeU64LE_sp_off d1.rwRange (0x50 + 8) regs.x25
  have d2 := d1.step64 (0x50 + 8) regs.x25
  have w2 := writeU64LE_sp_off d2.rwRange 0x60 regs.x24
  have d3 := d2.step64 0x60 regs.x24
  have w3 := writeU64LE_sp_off d3.rwRange (0x60 + 8) regs.x23
  have d4 := d3.step64 (0x60 + 8) regs.x23
  have w4 := writeU64LE_sp_off d4.rwRange 0x70 regs.x22
  have d5 := d4.step64 0x70 regs.x22
  have w5 := writeU64LE_sp_off d5.rwRange (0x70 + 8) regs.x21
  have d6 := d5.step64 (0x70 + 8) regs.x21
  have w6 := writeU64LE_sp_off d6.rwRange 0x80 regs.x20
  have d7 := d6.step64 0x80 regs.x20
  have w7 := writeU64LE_sp_off d7.rwRange (0x80 + 8) regs.x19
  have d8 := d7.step64 (0x80 + 8) regs.x19
  have w8 := writeU64LE_sp_off d8.rwRange 0x90 regs.x29
  have d9 := d8.step64 0x90 regs.x29
  have w9 := writeU64LE_sp_off d9.rwRange (0x90 + 8) regs.x30
  have d10 := d9.step64 (0x90 + 8) regs.x30
  refine ⟨_, ?_, d10, ?_⟩
  · f6_step step_hwFold6 hc 0 hwFold6Insn
    f6_step_with step_hwFold6 hc 1 hwFold6Insn [w0, w1]
    f6_step_with step_hwFold6 d2.codeLoaded 2 hwFold6Insn [w2, w3]
    f6_step_with step_hwFold6 d4.codeLoaded 3 hwFold6Insn [w4, w5]
    f6_step_with step_hwFold6 d6.codeLoaded 4 hwFold6Insn [w6, w7]
    f6_step_with step_hwFold6 d8.codeLoaded 5 hwFold6Insn [w8, w9]
    exact Arm64.run_zero _ _
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb
    · solve_slot_read hb

private theorem hwFold6_crc01 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {uoff blocks ws L L2 L3 L4 L5 : USize} {s_in : UInt32}
    (hsz : uoff.toNat + blocks.toNat * 384 ≤ a.size)
    (hws : ws.toNat = blocks.toNat * 8)
    (hL  : L.toNat = blocks.toNat * 64)
    (hL2 : L2.toNat = 2 * L.toNat)
    (hL3 : L3.toNat = 3 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat)
    (hL5 : L5.toNat = 5 * L.toNat)
    (hp1 : (uoff + L).toNat = uoff.toNat + L.toNat)
    (hp2 : (uoff + L2).toNat = uoff.toNat + L2.toNat)
    (hp3 : (uoff + L3).toNat = uoff.toNat + L3.toNat)
    (hp4 : (uoff + L4).toNat = uoff.toNat + L4.toNat)
    (hp5 : (uoff + L5).toNat = uoff.toNat + L5.toNat)
    (hc0 : uoff.toNat + 64 ≤ a.size)
    (hc1 : (uoff + L).toNat + 64 ≤ a.size)
    (hc2 : (uoff + L2).toNat + 64 ≤ a.size)
    (hc3 : (uoff + L3).toNat + 64 ≤ a.size)
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hpc : s.pc = Layout.hwFold6Base + 24)
    (hbase : objPtr + 0x18 = base)
    (hw0 : s.getW r0 = s_in)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = uoff.toUInt64)
    (hx3 : s.regs.x3 = blocks.toUInt64) :
    ∃ st1, Arm64.run code 46 s = some st1 ∧
      st1.pc = Layout.hwFold6Base + 208 ∧
      KeepMeta6 s st1 ∧
      st1.regs.x2 = uoff.toUInt64 ∧
      st1.regs.x3 = ws.toUInt64 ∧
      st1.regs.x4 = L.toUInt64 ∧
      st1.regs.x5 = L2.toUInt64 ∧
      st1.regs.x6 = L3.toUInt64 ∧
      st1.regs.x7 = L4.toUInt64 ∧
      st1.regs.x8 = objPtr ∧
      st1.regs.x9 = (uoff + L).toUInt64 ∧
      st1.regs.x10 = L5.toUInt64 ∧
      st1.getW r11 = Crc32c.crc512 a hs uoff hc0 s_in ∧
      st1.getW r12 = Crc32c.crc512 a hs (uoff + L) hc1 0 ∧
      st1.getW r0 = SimdModels.crc32c_u64 0 (b512w0 a hs (uoff + L2) hc2) ∧
      st1.regs.x16 = b512w1 a hs (uoff + L2) hc2 ∧
      st1.regs.x13 = base + (uoff + L2).toUInt64 ∧
      st1.regs.x19 = base + (uoff + L3).toUInt64 ∧
      st1.regs.x15 = b512w6 a hs (uoff + L3) hc3 ∧
      st1.regs.x1  = b512w7 a hs (uoff + L3) hc3 ∧
      st1.regs.x17 = base + (uoff + L4).toUInt64 ∧
      st1.regs.x14 = base + (uoff + L5).toUInt64 := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hw0 hx1 hx2 hx3 ⊢
  subst hpc
  have hus := usize_le_2pow64
  have sh_ws : blocks.toUInt64 <<< (3 : Nat).toUInt64 = ws.toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64, hws]
    change (blocks.toNat <<< 3) % 2 ^ 64 = blocks.toNat * 8
    rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  have sh_L : blocks.toUInt64 <<< (6 : Nat).toUInt64 = L.toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64, hL]
    change (blocks.toNat <<< 6) % 2 ^ 64 = blocks.toNat * 64
    rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  have sh_L2 : blocks.toUInt64 <<< (7 : Nat).toUInt64 = L2.toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64, hL2, hL]
    change (blocks.toNat <<< 7) % 2 ^ 64 = 2 * (blocks.toNat * 64)
    rw [Nat.shiftLeft_eq]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have sh_L4 : blocks.toUInt64 <<< (8 : Nat).toUInt64 = L4.toUInt64 := by
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64, hL4, hL]
    change (blocks.toNat <<< 8) % 2 ^ 64 = 4 * (blocks.toNat * 64)
    rw [Nat.shiftLeft_eq]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have sh_L3 : (blocks.toUInt64 + (blocks.toUInt64 <<< (1 : Nat).toUInt64)) <<< (6 : Nat).toUInt64 =
      L3.toUInt64 := by
    have h1 : (blocks.toUInt64 <<< (1 : Nat).toUInt64).toNat = blocks.toNat * 2 := by
      rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64]
      change (blocks.toNat <<< 1) % 2 ^ 64 = blocks.toNat * 2
      rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
    have hadd : (blocks.toUInt64 + (blocks.toUInt64 <<< (1 : Nat).toUInt64)).toNat = blocks.toNat * 3 := by
      rw [UInt64.toNat_add, USize.toNat_toUInt64, h1, Nat.mod_eq_of_lt (by omega)]; omega
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, hadd, USize.toNat_toUInt64, hL3, hL]
    change ((blocks.toNat * 3) <<< 6) % 2 ^ 64 = 3 * (blocks.toNat * 64)
    rw [Nat.shiftLeft_eq]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have sh_L5 : (blocks.toUInt64 + (blocks.toUInt64 <<< (2 : Nat).toUInt64)) <<< (6 : Nat).toUInt64 =
      L5.toUInt64 := by
    have h1 : (blocks.toUInt64 <<< (2 : Nat).toUInt64).toNat = blocks.toNat * 4 := by
      rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64]
      change (blocks.toNat <<< 2) % 2 ^ 64 = blocks.toNat * 4
      rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
    have hadd : (blocks.toUInt64 + (blocks.toUInt64 <<< (2 : Nat).toUInt64)).toNat = blocks.toNat * 5 := by
      rw [UInt64.toNat_add, USize.toNat_toUInt64, h1, Nat.mod_eq_of_lt (by omega)]; omega
    apply u64_ext
    rw [UInt64.toNat_shiftLeft, hadd, USize.toNat_toUInt64, hL5, hL]
    change ((blocks.toNat * 5) <<< 6) % 2 ^ 64 = 5 * (blocks.toNat * 64)
    rw [Nat.shiftLeft_eq]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have u_p1 : L.toUInt64 + uoff.toUInt64 = (uoff + L).toUInt64 := usize_add_toUInt64_eq hp1
  have u_p2 : uoff.toUInt64 + L2.toUInt64 = (uoff + L2).toUInt64 := usize_add_toUInt64_eq' hp2
  have u_p3 : uoff.toUInt64 + L3.toUInt64 = (uoff + L3).toUInt64 := usize_add_toUInt64_eq' hp3
  have u_p4 : uoff.toUInt64 + L4.toUInt64 = (uoff + L4).toUInt64 := usize_add_toUInt64_eq' hp4
  have u_p5 : uoff.toUInt64 + L5.toUInt64 = (uoff + L5).toUInt64 := usize_add_toUInt64_eq' hp5
  have b0 := block512Reads_of_ro hro hs uoff hc0
  have b1 := block512Reads_of_ro hro hs (uoff + L) hc1
  have b2 := block512Reads_of_ro hro hs (uoff + L2) hc2
  have b3 := block512Reads_of_ro hro hs (uoff + L3) hc3
  apply Exists.intro
  apply And.intro
  · f6_step step_hwFold6 hc 6 hwFold6Insn
    f6_step_with step_hwFold6 hc 7 hwFold6Insn [hx3]
    f6_step_with step_hwFold6 hc 8 hwFold6Insn [hx1]
    f6_step_with step_hwFold6 hc 9 hwFold6Insn [hx3, sh_L2]
    f6_step_with step_hwFold6 hc 10 hwFold6Insn [hx1, hbase]
    f6_step_with step_hwFold6 hc 11 hwFold6Insn [hx2]
    f6_step_with step_hwFold6 hc 12 hwFold6Insn [u_p2]
    f6_step_with step_hwFold6 hc 13 hwFold6Insn [b0.r0, b0.r1]
    f6_step_with step_hwFold6 hc 14 hwFold6Insn [b0.r2, b0.r3]
    f6_step_with step_hwFold6 hc 15 hwFold6Insn [hx3, sh_ws]
    f6_step_with step_hwFold6 hc 16 hwFold6Insn [sh_L]
    f6_step_with step_hwFold6 hc 17 hwFold6Insn [b0.r4, b0.r5]
    f6_step step_hwFold6 hc 18 hwFold6Insn
    f6_step_with step_hwFold6 hc 19 hwFold6Insn [sh_L3]
    f6_step_with step_hwFold6 hc 20 hwFold6Insn [sh_L4]
    f6_step_with step_hwFold6 hc 21 hwFold6Insn [b0.r6, b0.r7]
    f6_step step_hwFold6 hc 22 hwFold6Insn
    f6_step_with step_hwFold6 hc 23 hwFold6Insn [hx2, u_p1]
    f6_step step_hwFold6 hc 24 hwFold6Insn
    f6_step_with step_hwFold6 hc 25 hwFold6Insn [b1.r0, b1.r1]
    f6_step_with step_hwFold6 hc 26 hwFold6Insn [sh_L5]
    f6_step step_hwFold6 hc 27 hwFold6Insn
    f6_step step_hwFold6 hc 28 hwFold6Insn
    f6_step step_hwFold6 hc 29 hwFold6Insn
    f6_step_with step_hwFold6 hc 30 hwFold6Insn [b1.r2, b1.r3]
    f6_step step_hwFold6 hc 31 hwFold6Insn
    f6_step step_hwFold6 hc 32 hwFold6Insn
    f6_step step_hwFold6 hc 33 hwFold6Insn
    f6_step step_hwFold6 hc 34 hwFold6Insn
    f6_step_with step_hwFold6 hc 35 hwFold6Insn [b1.r4, b1.r5]
    f6_step step_hwFold6 hc 36 hwFold6Insn
    f6_step step_hwFold6 hc 37 hwFold6Insn
    f6_step step_hwFold6 hc 38 hwFold6Insn
    f6_step step_hwFold6 hc 39 hwFold6Insn
    f6_step_with step_hwFold6 hc 40 hwFold6Insn [b1.r6, b1.r7]
    f6_step step_hwFold6 hc 41 hwFold6Insn
    f6_step step_hwFold6 hc 42 hwFold6Insn
    f6_step step_hwFold6 hc 43 hwFold6Insn
    f6_step step_hwFold6 hc 44 hwFold6Insn
    f6_step_with step_hwFold6 hc 45 hwFold6Insn [b2.r0, b2.r1]
    f6_step step_hwFold6 hc 46 hwFold6Insn
    f6_step step_hwFold6 hc 47 hwFold6Insn
    f6_step_with step_hwFold6 hc 48 hwFold6Insn [u_p3]
    f6_step_with step_hwFold6 hc 49 hwFold6Insn [b3.r6, b3.r7]
    f6_step_with step_hwFold6 hc 50 hwFold6Insn [u_p4]
    f6_step_with step_hwFold6 hc 51 hwFold6Insn [u_p5]
    exact Arm64.run_zero _ _
  · dsimp only [getW_mk_r0, getW_mk_r11, getW_mk_r12] at hw0 ⊢
    rw [hw0, b512_crc512, b512_crc512]
    exact ⟨rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      toUInt32_toUInt64 _, toUInt32_toUInt64 _, toUInt32_toUInt64 _,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private structure Fold6Consts (s : Arm64.ArmState) : Prop where
  v0 : s.simd.v0 = V128.ofHalves Crc32c.kFold384_1 0
  v1 : s.simd.v1 = V128.ofHalves Crc32c.kFold384_2 0
  v2 : s.simd.v2 = V128.ofHalves Crc32c.kFold256_1 0
  v3 : s.simd.v3 = V128.ofHalves Crc32c.kFold256_2 0
  v4 : s.simd.v4 = V128.ofHalves Crc32c.kFold128_1 0
  v5 : s.simd.v5 = V128.ofHalves Crc32c.kFold128_2 0

private structure KeepRegs6 (s s' : Arm64.ArmState) : Prop where
  x2  : s'.regs.x2 = s.regs.x2
  x3  : s'.regs.x3 = s.regs.x3
  x4  : s'.regs.x4 = s.regs.x4
  x5  : s'.regs.x5 = s.regs.x5
  x6  : s'.regs.x6 = s.regs.x6
  x7  : s'.regs.x7 = s.regs.x7
  x8  : s'.regs.x8 = s.regs.x8
  x9  : s'.regs.x9 = s.regs.x9
  x10 : s'.regs.x10 = s.regs.x10
  w11 : s'.getW r11 = s.getW r11
  w12 : s'.getW r12 = s.getW r12

private theorem KeepRegs6.trans {s1 s2 s3 : Arm64.ArmState}
    (h12 : KeepRegs6 s1 s2) (h23 : KeepRegs6 s2 s3) : KeepRegs6 s1 s3 :=
  ⟨h23.x2.trans h12.x2, h23.x3.trans h12.x3, h23.x4.trans h12.x4, h23.x5.trans h12.x5,
   h23.x6.trans h12.x6, h23.x7.trans h12.x7, h23.x8.trans h12.x8, h23.x9.trans h12.x9,
   h23.x10.trans h12.x10, h23.w11.trans h12.w11, h23.w12.trans h12.w12⟩

private theorem hwFold6_s3 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {p2 p3 : USize}
    (hc2 : p2.toNat + 64 ≤ a.size)
    (hc3 : p3.toNat + 64 ≤ a.size)
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hpc : s.pc = Layout.hwFold6Base + 208)
    (hw0 : s.getW r0 = SimdModels.crc32c_u64 0 (b512w0 a hs p2 hc2))
    (hx16 : s.regs.x16 = b512w1 a hs p2 hc2)
    (hx19 : s.regs.x19 = base + p3.toUInt64)
    (hx15 : s.regs.x15 = b512w6 a hs p3 hc3)
    (hx1  : s.regs.x1  = b512w7 a hs p3 hc3) :
    ∃ k st1, Arm64.run code k s = some st1 ∧
      st1.pc = Layout.hwFold6Base + 400 ∧
      KeepMeta6 s st1 ∧
      KeepRegs6 s st1 ∧
      Fold6Consts st1 ∧
      st1.getW r0 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64 0 (b512w0 a hs p2 hc2))
        (b512w1 a hs p2 hc2) ∧
      st1.regs.x13 = s.regs.x13 ∧
      st1.regs.x17 = s.regs.x17 ∧
      st1.regs.x14 = s.regs.x14 ∧
      st1.regs.x15 = Crc32c.init512Lo
        (b512w0 a hs p3 hc3) (b512w1 a hs p3 hc3)
        (b512w2 a hs p3 hc3) (b512w3 a hs p3 hc3)
        (b512w4 a hs p3 hc3) (b512w5 a hs p3 hc3)
        (b512w6 a hs p3 hc3) ∧
      st1.regs.x16 = Crc32c.init512Hi
        (b512w0 a hs p3 hc3) (b512w1 a hs p3 hc3)
        (b512w2 a hs p3 hc3) (b512w3 a hs p3 hc3)
        (b512w4 a hs p3 hc3) (b512w5 a hs p3 hc3)
        (b512w7 a hs p3 hc3) := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hro hpc hw0 hx16 hx19 hx15 hx1 ⊢
  subst hpc
  have g52 := hc.hwFold6.2.2 { idx := 52, rd := r20, target := .gKFold384_1 } (by decide)
  have g54 := hc.hwFold6.2.2 { idx := 54, rd := r21, target := .gKFold384_2 } (by decide)
  have g63 := hc.hwFold6.2.2 { idx := 63, rd := r21, target := .gKFold256_1 } (by decide)
  have g67 := hc.hwFold6.2.2 { idx := 67, rd := r25, target := .gKFold256_2 } (by decide)
  have g73 := hc.hwFold6.2.2 { idx := 73, rd := r21, target := .gKFold128_1 } (by decide)
  have g75 := hc.hwFold6.2.2 { idx := 75, rd := r25, target := .gKFold128_2 } (by decide)
  have rk384_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold384_1
  have rk384_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold384_2
  have rk256_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold256_1
  have rk256_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold256_2
  have rk128_1 := Arm64.Mem.hasROU64_readU64LE hg.kFold128_1
  have rk128_2 := Arm64.Mem.hasROU64_readU64LE hg.kFold128_2
  have b3 := block512Reads_of_ro hro hs p3 hc3
  f6_gotPair g52
  f6_gotPair g54
  f6_step_ex_with step_hwFold6 hc 56 hwFold6Insn [rk384_1]
  f6_step_ex_with step_hwFold6 hc 57 hwFold6Insn [hx19, b3.r0, b3.r1]
  f6_step_ex step_hwFold6 hc 58 hwFold6Insn
  f6_step_ex step_hwFold6 hc 59 hwFold6Insn
  f6_step_ex step_hwFold6 hc 60 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 61 hwFold6Insn [rk384_2]
  f6_step_ex step_hwFold6 hc 62 hwFold6Insn
  f6_gotPair g63
  f6_step_ex step_hwFold6 hc 65 hwFold6Insn
  f6_step_ex step_hwFold6 hc 66 hwFold6Insn
  f6_gotPair g67
  f6_step_ex_with step_hwFold6 hc 69 hwFold6Insn [rk256_1]
  f6_step_ex_with step_hwFold6 hc 70 hwFold6Insn [hx19, b3.r2, b3.r3]
  f6_step_ex step_hwFold6 hc 71 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 72 hwFold6Insn [rk256_2]
  f6_gotPair g73
  f6_gotPair g75
  f6_step_ex step_hwFold6 hc 77 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 78 hwFold6Insn [rk128_1]
  f6_step_ex_with step_hwFold6 hc 79 hwFold6Insn [hx19, b3.r4, b3.r5]
  f6_step_ex step_hwFold6 hc 80 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 81 hwFold6Insn [rk128_2]
  f6_step_ex step_hwFold6 hc 82 hwFold6Insn
  f6_step_ex step_hwFold6 hc 83 hwFold6Insn
  f6_step_ex step_hwFold6 hc 84 hwFold6Insn
  f6_step_ex step_hwFold6 hc 85 hwFold6Insn
  f6_step_ex step_hwFold6 hc 86 hwFold6Insn
  f6_step_ex step_hwFold6 hc 87 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 88 hwFold6Insn [hx15]
  f6_step_ex step_hwFold6 hc 89 hwFold6Insn
  f6_step_ex step_hwFold6 hc 90 hwFold6Insn
  f6_step_ex step_hwFold6 hc 91 hwFold6Insn
  f6_step_ex step_hwFold6 hc 92 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 93 hwFold6Insn [hx16]
  f6_step_ex step_hwFold6 hc 94 hwFold6Insn
  f6_step_ex step_hwFold6 hc 95 hwFold6Insn
  f6_step_ex step_hwFold6 hc 96 hwFold6Insn
  f6_step_ex step_hwFold6 hc 97 hwFold6Insn
  f6_step_ex_with step_hwFold6 hc 98 hwFold6Insn [hx1]
  f6_step_ex step_hwFold6 hc 99 hwFold6Insn
  refine ⟨0, _, Arm64.run_zero _ _, ?_⟩
  dsimp only [getW_mk_r0, getW_mk_r11, getW_mk_r12] at hw0 ⊢
  rw [hw0, toUInt32_toUInt64]
  refine ⟨rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold Crc32c.init512Lo Crc32c.fold128Lo; dsimp only; ac_rfl
  · unfold Crc32c.init512Hi Crc32c.fold128Hi; dsimp only; ac_rfl

private theorem hwFold6_s4 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {p2 p4 : USize}
    (hc2 : p2.toNat + 64 ≤ a.size)
    (hc4 : p4.toNat + 64 ≤ a.size)
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hk : Fold6Consts s)
    (hpc : s.pc = Layout.hwFold6Base + 400)
    (hw0 : s.getW r0 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64 0 (b512w0 a hs p2 hc2))
      (b512w1 a hs p2 hc2))
    (hx13 : s.regs.x13 = base + p2.toUInt64)
    (hx17 : s.regs.x17 = base + p4.toUInt64) :
    ∃ st1, Arm64.run code 38 s = some st1 ∧
      st1.pc = Layout.hwFold6Base + 552 ∧
      KeepMeta6 s st1 ∧
      KeepRegs6 s st1 ∧
      Fold6Consts st1 ∧
      st1.getW r1 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
        (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
          (SimdModels.crc32c_u64 0 (b512w0 a hs p2 hc2)) (b512w1 a hs p2 hc2))
          (b512w2 a hs p2 hc2)) (b512w3 a hs p2 hc2))
          (b512w4 a hs p2 hc2)) (b512w5 a hs p2 hc2)) (b512w6 a hs p2 hc2) ∧
      st1.regs.x13 = b512w7 a hs p2 hc2 ∧
      st1.regs.x14 = s.regs.x14 ∧
      st1.regs.x15 = s.regs.x15 ∧
      st1.regs.x16 = s.regs.x16 ∧
      st1.regs.x17 = Crc32c.init512Lo
        (b512w0 a hs p4 hc4) (b512w1 a hs p4 hc4)
        (b512w2 a hs p4 hc4) (b512w3 a hs p4 hc4)
        (b512w4 a hs p4 hc4) (b512w5 a hs p4 hc4)
        (b512w6 a hs p4 hc4) ∧
      st1.regs.x0 = Crc32c.init512Hi
        (b512w0 a hs p4 hc4) (b512w1 a hs p4 hc4)
        (b512w2 a hs p4 hc4) (b512w3 a hs p4 hc4)
        (b512w4 a hs p4 hc4) (b512w5 a hs p4 hc4)
        (b512w7 a hs p4 hc4) := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  rcases hk with ⟨hv0, hv1, hv2, hv3, hv4, hv5⟩
  dsimp only at hc hro hpc hw0 hx13 hx17 hv0 hv1 hv2 hv3 hv4 hv5 ⊢
  subst hpc
  have b2 := block512Reads_of_ro hro hs p2 hc2
  have b4 := block512Reads_of_ro hro hs p4 hc4
  apply Exists.intro
  apply And.intro
  · f6_step_with step_hwFold6 hc 100 hwFold6Insn [hx17, b4.r0, b4.r1]
    f6_step_with step_hwFold6 hc 101 hwFold6Insn [hv0]
    f6_step step_hwFold6 hc 102 hwFold6Insn
    f6_step step_hwFold6 hc 103 hwFold6Insn
    f6_step_with step_hwFold6 hc 104 hwFold6Insn [hv1]
    f6_step step_hwFold6 hc 105 hwFold6Insn
    f6_step step_hwFold6 hc 106 hwFold6Insn
    f6_step_with step_hwFold6 hc 107 hwFold6Insn [hx17, b4.r2, b4.r3]
    f6_step_with step_hwFold6 hc 108 hwFold6Insn [hv2]
    f6_step_with step_hwFold6 hc 109 hwFold6Insn [hv3]
    f6_step_with step_hwFold6 hc 110 hwFold6Insn [hx13, b2.r2, b2.r3]
    f6_step step_hwFold6 hc 111 hwFold6Insn
    f6_step_with step_hwFold6 hc 112 hwFold6Insn [hx17, b4.r4, b4.r5]
    f6_step_with step_hwFold6 hc 113 hwFold6Insn [hv4]
    f6_step_with step_hwFold6 hc 114 hwFold6Insn [hv5]
    f6_step step_hwFold6 hc 115 hwFold6Insn
    f6_step step_hwFold6 hc 116 hwFold6Insn
    f6_step step_hwFold6 hc 117 hwFold6Insn
    f6_step step_hwFold6 hc 118 hwFold6Insn
    f6_step step_hwFold6 hc 119 hwFold6Insn
    f6_step step_hwFold6 hc 120 hwFold6Insn
    f6_step_with step_hwFold6 hc 121 hwFold6Insn [hx13, b2.r4, b2.r5]
    f6_step step_hwFold6 hc 122 hwFold6Insn
    f6_step_with step_hwFold6 hc 123 hwFold6Insn [hx17, b4.r6, b4.r7]
    f6_step step_hwFold6 hc 124 hwFold6Insn
    f6_step step_hwFold6 hc 125 hwFold6Insn
    f6_step step_hwFold6 hc 126 hwFold6Insn
    f6_step step_hwFold6 hc 127 hwFold6Insn
    f6_step step_hwFold6 hc 128 hwFold6Insn
    f6_step step_hwFold6 hc 129 hwFold6Insn
    f6_step step_hwFold6 hc 130 hwFold6Insn
    f6_step step_hwFold6 hc 131 hwFold6Insn
    f6_step step_hwFold6 hc 132 hwFold6Insn
    f6_step step_hwFold6 hc 133 hwFold6Insn
    f6_step step_hwFold6 hc 134 hwFold6Insn
    f6_step step_hwFold6 hc 135 hwFold6Insn
    f6_step_with step_hwFold6 hc 136 hwFold6Insn [hx13, b2.r6, b2.r7]
    f6_step step_hwFold6 hc 137 hwFold6Insn
    exact Arm64.run_zero _ _
  · dsimp only [getW_mk_r0, getW_mk_r1, getW_mk_r11, getW_mk_r12] at hw0 ⊢
    rw [hw0, toUInt32_toUInt64]
    refine ⟨rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · unfold Crc32c.init512Lo Crc32c.fold128Lo; dsimp only; ac_rfl
    · unfold Crc32c.init512Hi Crc32c.fold128Hi; dsimp only; ac_rfl

private theorem hwFold6_s5_prep {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {p2 p5 : USize}
    (hc2 : p2.toNat + 64 ≤ a.size)
    (hc5 : p5.toNat + 64 ≤ a.size)
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes base a)
    (hk : Fold6Consts s)
    (hpc : s.pc = Layout.hwFold6Base + 552)
    (hw1 : s.getW r1 = SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
      (SimdModels.crc32c_u64 (SimdModels.crc32c_u64 (SimdModels.crc32c_u64
        (SimdModels.crc32c_u64 0 (b512w0 a hs p2 hc2)) (b512w1 a hs p2 hc2))
        (b512w2 a hs p2 hc2)) (b512w3 a hs p2 hc2))
        (b512w4 a hs p2 hc2)) (b512w5 a hs p2 hc2)) (b512w6 a hs p2 hc2))
    (hx13 : s.regs.x13 = b512w7 a hs p2 hc2)
    (hx14 : s.regs.x14 = base + p5.toUInt64) :
    ∃ st1, Arm64.run code 31 s = some st1 ∧
      st1.pc = Layout.hwFold6Base + 676 ∧
      KeepMeta6 s st1 ∧
      KeepRegs6 s st1 ∧
      st1.getW r13 = Crc32c.crc512 a hs p2 hc2 0 ∧
      st1.regs.x15 = s.regs.x15 ∧
      st1.regs.x16 = s.regs.x16 ∧
      st1.regs.x17 = s.regs.x17 ∧
      st1.regs.x0  = s.regs.x0 ∧
      st1.regs.x19 = Crc32c.init512Lo
        (b512w0 a hs p5 hc5) (b512w1 a hs p5 hc5)
        (b512w2 a hs p5 hc5) (b512w3 a hs p5 hc5)
        (b512w4 a hs p5 hc5) (b512w5 a hs p5 hc5)
        (b512w6 a hs p5 hc5) ∧
      st1.regs.x14 = Crc32c.init512Hi
        (b512w0 a hs p5 hc5) (b512w1 a hs p5 hc5)
        (b512w2 a hs p5 hc5) (b512w3 a hs p5 hc5)
        (b512w4 a hs p5 hc5) (b512w5 a hs p5 hc5)
        (b512w7 a hs p5 hc5) := by
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  rcases hk with ⟨hv0, hv1, hv2, hv3, hv4, hv5⟩
  dsimp only at hc hro hpc hw1 hx13 hx14 hv0 hv1 hv2 hv3 hv4 hv5 ⊢
  subst hpc
  have b5 := block512Reads_of_ro hro hs p5 hc5
  apply Exists.intro
  apply And.intro
  · f6_step_with step_hwFold6 hc 138 hwFold6Insn [hx14, b5.r0, b5.r1]
    f6_step_with step_hwFold6 hc 139 hwFold6Insn [hv0]
    f6_step step_hwFold6 hc 140 hwFold6Insn
    f6_step step_hwFold6 hc 141 hwFold6Insn
    f6_step step_hwFold6 hc 142 hwFold6Insn
    f6_step_with step_hwFold6 hc 143 hwFold6Insn [hv1]
    f6_step step_hwFold6 hc 144 hwFold6Insn
    f6_step step_hwFold6 hc 145 hwFold6Insn
    f6_step_with step_hwFold6 hc 146 hwFold6Insn [hx14, b5.r2, b5.r3]
    f6_step_with step_hwFold6 hc 147 hwFold6Insn [hv2]
    f6_step_with step_hwFold6 hc 148 hwFold6Insn [hv3]
    f6_step_with step_hwFold6 hc 149 hwFold6Insn [hx14, b5.r4, b5.r5]
    f6_step_with step_hwFold6 hc 150 hwFold6Insn [hv4]
    f6_step_with step_hwFold6 hc 151 hwFold6Insn [hv5]
    f6_step step_hwFold6 hc 152 hwFold6Insn
    f6_step step_hwFold6 hc 153 hwFold6Insn
    f6_step step_hwFold6 hc 154 hwFold6Insn
    f6_step step_hwFold6 hc 155 hwFold6Insn
    f6_step step_hwFold6 hc 156 hwFold6Insn
    f6_step_with step_hwFold6 hc 157 hwFold6Insn [hx14, b5.r6, b5.r7]
    f6_step step_hwFold6 hc 158 hwFold6Insn
    f6_step step_hwFold6 hc 159 hwFold6Insn
    f6_step step_hwFold6 hc 160 hwFold6Insn
    f6_step step_hwFold6 hc 161 hwFold6Insn
    f6_step step_hwFold6 hc 162 hwFold6Insn
    f6_step step_hwFold6 hc 163 hwFold6Insn
    f6_step step_hwFold6 hc 164 hwFold6Insn
    f6_step step_hwFold6 hc 165 hwFold6Insn
    f6_step step_hwFold6 hc 166 hwFold6Insn
    f6_step step_hwFold6 hc 167 hwFold6Insn
    f6_step step_hwFold6 hc 168 hwFold6Insn
    exact Arm64.run_zero _ _
  · dsimp only [getW_mk_r1, getW_mk_r11, getW_mk_r12, getW_mk_r13] at hw1 ⊢
    rw [hw1, hx13, b512_crc512, toUInt32_toUInt64]
    refine ⟨rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · unfold Crc32c.init512Lo Crc32c.fold128Lo; dsimp only; ac_rfl
    · unfold Crc32c.init512Hi Crc32c.fold128Hi; dsimp only; ac_rfl

/-- Machine-code specification of `_lp_leancrc32c_Crc32c_hwFold6___redArg` (`186` insns):
executes from `Layout.hwFold6Base` to caller return address `s.regs.x30`, placing
`Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + blocks.toNat * 384))`
in `W0`, touching only the 256-byte combined stack region `[s.sp - 0x100, s.sp)`
(`0xa0` in `hwFold6` + `0x60` in `hwFold6Loop`), and preserving all AAPCS64
callee-saved registers (`CalleeSaved s s'`). -/
theorem hwFold6_mc_spec {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {uoff blocks : USize} {s_in : UInt32}
    (hb1 : 1 ≤ blocks.toNat)
    (hsz : uoff.toNat + blocks.toNat * 384 ≤ a.size)
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.hwFold6Base)
    (hsp_lo : 0x100 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x100) 0x100)
    (hw0 : s.getW r0 = s_in)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = uoff.toUInt64)
    (hx3 : s.regs.x3 = blocks.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + blocks.toNat * 384)) ∧
      StackDelta code Layout s.mem s'.mem (s.sp - 0x100) 0x100 ∧
      CalleeSaved s s' := by
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e64 : (64 : USize).toNat = 64 := by simp
  have e8 : (8 : USize).toNat = 8 := by simp
  have e5 : (5 : USize).toNat = 5 := by simp
  have e4 : (4 : USize).toNat = 4 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  let ws := blocks * 8
  let L := blocks * 64
  let L2 := 2 * L
  let L3 := 3 * L
  let L4 := 4 * L
  let L5 := 5 * L
  have hws : ws.toNat = blocks.toNat * 8 := by
    show (blocks * 8).toNat = _; rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
  have hL : L.toNat = blocks.toNat * 64 := by
    show (blocks * 64).toNat = _; rw [USize.toNat_mul, e64]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : L2.toNat = 2 * L.toNat := by
    show (2 * L).toNat = _; rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : L3.toNat = 3 * L.toNat := by
    show (3 * L).toNat = _; rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hL4 : L4.toNat = 4 * L.toNat := by
    show (4 * L).toNat = _; rw [USize.toNat_mul, e4]; exact Nat.mod_eq_of_lt (by omega)
  have hL5 : L5.toNat = 5 * L.toNat := by
    show (5 * L).toNat = _; rw [USize.toNat_mul, e5]; exact Nat.mod_eq_of_lt (by omega)
  have hu64 : (uoff + 64).toNat = uoff.toNat + 64 := Crc32c.usize_add_toNat uoff 64 (by omega)
  have hp1 : (uoff + L).toNat = uoff.toNat + L.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp2 : (uoff + L2).toNat = uoff.toNat + L2.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (uoff + L3).toNat = uoff.toNat + L3.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp4 : (uoff + L4).toNat = uoff.toNat + L4.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp5 : (uoff + L5).toNat = uoff.toNat + L5.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hle_loop : (uoff + 64).toNat ≤ (uoff + L).toNat := by omega
  have hal_loop : ((uoff + L).toNat - (uoff + 64).toNat) % 64 = 0 := by omega
  have hLend : (uoff + L).toNat + 5 * L.toNat ≤ a.size := by omega
  have hc0 : uoff.toNat + 64 ≤ a.size := by omega
  have hc1 : (uoff + L).toNat + 64 ≤ a.size := by omega
  have hc2 : (uoff + L2).toNat + 64 ≤ a.size := by omega
  have hc3 : (uoff + L3).toNat + 64 ≤ a.size := by omega
  have hc4 : (uoff + L4).toNat + 64 ≤ a.size := by omega
  have hc5 : (uoff + L5).toNat + 64 ≤ a.size := by omega
  have hfold_eq : Crc32c.hwFold6Loop a hs (uoff + 64) (uoff + L) ws L L2 L3 L4 L5
      hle_loop hal_loop hL2 hL3 hL4 hL5 hLend
      (Crc32c.crc512 a hs uoff hc0 s_in)
      (Crc32c.crc512 a hs (uoff + L) hc1 0)
      (Crc32c.crc512 a hs (uoff + L2) hc2 0)
      (Crc32c.init512Lo (b512w0 a hs (uoff + L3) hc3) (b512w1 a hs (uoff + L3) hc3)
        (b512w2 a hs (uoff + L3) hc3) (b512w3 a hs (uoff + L3) hc3)
        (b512w4 a hs (uoff + L3) hc3) (b512w5 a hs (uoff + L3) hc3) (b512w6 a hs (uoff + L3) hc3))
      (Crc32c.init512Hi (b512w0 a hs (uoff + L3) hc3) (b512w1 a hs (uoff + L3) hc3)
        (b512w2 a hs (uoff + L3) hc3) (b512w3 a hs (uoff + L3) hc3)
        (b512w4 a hs (uoff + L3) hc3) (b512w5 a hs (uoff + L3) hc3) (b512w7 a hs (uoff + L3) hc3))
      (Crc32c.init512Lo (b512w0 a hs (uoff + L4) hc4) (b512w1 a hs (uoff + L4) hc4)
        (b512w2 a hs (uoff + L4) hc4) (b512w3 a hs (uoff + L4) hc4)
        (b512w4 a hs (uoff + L4) hc4) (b512w5 a hs (uoff + L4) hc4) (b512w6 a hs (uoff + L4) hc4))
      (Crc32c.init512Hi (b512w0 a hs (uoff + L4) hc4) (b512w1 a hs (uoff + L4) hc4)
        (b512w2 a hs (uoff + L4) hc4) (b512w3 a hs (uoff + L4) hc4)
        (b512w4 a hs (uoff + L4) hc4) (b512w5 a hs (uoff + L4) hc4) (b512w7 a hs (uoff + L4) hc4))
      (Crc32c.init512Lo (b512w0 a hs (uoff + L5) hc5) (b512w1 a hs (uoff + L5) hc5)
        (b512w2 a hs (uoff + L5) hc5) (b512w3 a hs (uoff + L5) hc5)
        (b512w4 a hs (uoff + L5) hc5) (b512w5 a hs (uoff + L5) hc5) (b512w6 a hs (uoff + L5) hc5))
      (Crc32c.init512Hi (b512w0 a hs (uoff + L5) hc5) (b512w1 a hs (uoff + L5) hc5)
        (b512w2 a hs (uoff + L5) hc5) (b512w3 a hs (uoff + L5) hc5)
        (b512w4 a hs (uoff + L5) hc5) (b512w5 a hs (uoff + L5) hc5) (b512w7 a hs (uoff + L5) hc5)) =
      Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + blocks.toNat * 384)) := by
    rw [← Crc32c.hwFold6_eq s_in a hs uoff blocks hb1 hsz]
    unfold Crc32c.hwFold6
    simp only [withBlock512_eq_b512]; rfl
  have hsp_100 : (s.sp - 0x100).toNat = s.sp.toNat - 0x100 := by
    have hle : (0x100 : UInt64) ≤ s.sp := by change 0x100 ≤ s.sp.toNat; omega
    exact UInt64.toNat_sub_of_le _ _ hle
  have hsp_a0 : (s.sp - 0xa0).toNat = s.sp.toNat - 0xa0 := by
    have hle : (0xa0 : UInt64) ≤ s.sp := by change 0xa0 ≤ s.sp.toNat; omega
    exact UInt64.toNat_sub_of_le _ _ hle
  have hrw_a0 : s.mem.isRWRange (s.sp - 0xa0) 0xa0 :=
    isRWRange_sub hrw (by omega) (by omega)
  have d_full0 := StackDelta.refl hrw hc hg
  rcases hwFold6_prologue hc hg hpc hrw_a0 with ⟨mPro, hpro, d_pro, hsaved_pro⟩
  obtain ⟨base, hbase⟩ : ∃ base : UInt64, objPtr + 0x18 = base := ⟨objPtr + 0x18, rfl⟩
  rw [hbase] at hro
  have hcP := d_pro.codeLoaded
  have hgP := d_pro.globalsLoaded
  have hroP := d_pro.hasROBytes hro
  rcases hwFold6_crc01 (s := { s with sp := s.sp - 0xa0, pc := Layout.hwFold6Base + 24, mem := mPro })
      hs hsz hws hL hL2 hL3 hL4 hL5 hp1 hp2 hp3 hp4 hp5 hc0 hc1 hc2 hc3
      hcP hroP rfl hbase hw0 hx1 hx2 hx3 with
    ⟨st1, hr1, hpc1, hkm1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1, hx10_1,
     hw11_1, hw12_1, hw0_1, hx16_1, hx13_1, hx19_1, hx15_1, hx1_1, hx17_1, hx14_1⟩
  have hm1 : st1.mem = mPro := hkm1.mem
  rcases hwFold6_s3 hs hc2 hc3 (hm1 ▸ hcP) (hm1 ▸ hgP) (hm1 ▸ hroP) hpc1
      hw0_1 hx16_1 hx19_1 hx15_1 hx1_1 with
    ⟨ks3, st2, hr2, hpc2, hkm2, hkr2, hk2, hw0_2, hx13_2, hx17_2, hx14_2, hx15_2, hx16_2⟩
  have hkm12 := hkm1.trans hkm2
  have hm2 : st2.mem = mPro := hkm12.mem
  rcases hwFold6_s4 hs hc2 hc4 (hm2 ▸ hcP) (hm2 ▸ hroP) hk2 hpc2
      hw0_2 (hx13_2.trans hx13_1) (hx17_2.trans hx17_1) with
    ⟨st3, hr3, hpc3, hkm3, hkr3, hk3, hw1_3, hx13_3, hx14_3, hx15_3, hx16_3, hx17_3, hx0_3⟩
  have hkm13 := hkm12.trans hkm3
  have hm3 : st3.mem = mPro := hkm13.mem
  rcases hwFold6_s5_prep hs hc2 hc5 (hm3 ▸ hcP) (hm3 ▸ hroP) hk3 hpc3
      hw1_3 hx13_3 (hx14_3.trans (hx14_2.trans hx14_1)) with
    ⟨st4, hr4, hpc4, hkm4, hkr4, hw13_4, hx15_4, hx16_4, hx17_4, hx0_4, hx19_4, hx14_4⟩
  have hkm := hkm13.trans hkm4
  have hkr := (hkr2.trans hkr3).trans hkr4
  have hm4 : st4.mem = mPro := hkm.mem
  refine run_bind_exists hpro
    (run_bind_exists hr1 (run_bind_exists hr2 (run_bind_exists hr3 (run_bind_exists hr4 ?_))))
  -- Stack-argument writes (`idx 169..177`) + `bl hwFold6Loop` (`idx 178`) + epilogue (`idx 179..185`)
  let sp0 := s.sp - 0xa0
  have hsp0_nat : sp0.toNat = s.sp.toNat - 0xa0 := hsp_a0
  have hsp4 : st4.sp = sp0 := hkm.sp
  have hb_a0 : sp0.toNat + 0xa0 ≤ UInt64.size := d_pro.rwRange.1
  have hrw_args : mPro.isRWRange sp0 0x48 := isRWRange_sub d_pro.rwRange (by omega) (by omega)
  let s0v := Crc32c.crc512 a hs uoff hc0 s_in
  let s1v := Crc32c.crc512 a hs (uoff + L) hc1 0
  let s2v := Crc32c.crc512 a hs (uoff + L2) hc2 0
  let a0v := Crc32c.init512Lo (b512w0 a hs (uoff + L3) hc3) (b512w1 a hs (uoff + L3) hc3)
    (b512w2 a hs (uoff + L3) hc3) (b512w3 a hs (uoff + L3) hc3)
    (b512w4 a hs (uoff + L3) hc3) (b512w5 a hs (uoff + L3) hc3) (b512w6 a hs (uoff + L3) hc3)
  let a1v := Crc32c.init512Hi (b512w0 a hs (uoff + L3) hc3) (b512w1 a hs (uoff + L3) hc3)
    (b512w2 a hs (uoff + L3) hc3) (b512w3 a hs (uoff + L3) hc3)
    (b512w4 a hs (uoff + L3) hc3) (b512w5 a hs (uoff + L3) hc3) (b512w7 a hs (uoff + L3) hc3)
  let b0v := Crc32c.init512Lo (b512w0 a hs (uoff + L4) hc4) (b512w1 a hs (uoff + L4) hc4)
    (b512w2 a hs (uoff + L4) hc4) (b512w3 a hs (uoff + L4) hc4)
    (b512w4 a hs (uoff + L4) hc4) (b512w5 a hs (uoff + L4) hc4) (b512w6 a hs (uoff + L4) hc4)
  let b1v := Crc32c.init512Hi (b512w0 a hs (uoff + L4) hc4) (b512w1 a hs (uoff + L4) hc4)
    (b512w2 a hs (uoff + L4) hc4) (b512w3 a hs (uoff + L4) hc4)
    (b512w4 a hs (uoff + L4) hc4) (b512w5 a hs (uoff + L4) hc4) (b512w7 a hs (uoff + L4) hc4)
  let c0v := Crc32c.init512Lo (b512w0 a hs (uoff + L5) hc5) (b512w1 a hs (uoff + L5) hc5)
    (b512w2 a hs (uoff + L5) hc5) (b512w3 a hs (uoff + L5) hc5)
    (b512w4 a hs (uoff + L5) hc5) (b512w5 a hs (uoff + L5) hc5) (b512w6 a hs (uoff + L5) hc5)
  let c1v := Crc32c.init512Hi (b512w0 a hs (uoff + L5) hc5) (b512w1 a hs (uoff + L5) hc5)
    (b512w2 a hs (uoff + L5) hc5) (b512w3 a hs (uoff + L5) hc5)
    (b512w4 a hs (uoff + L5) hc5) (b512w5 a hs (uoff + L5) hc5) (b512w7 a hs (uoff + L5) hc5)
  have hx2_4   : st4.regs.x2  = uoff.toUInt64 := hkr.x2.trans hx2_1
  have hx3_4   : st4.regs.x3  = ws.toUInt64 := hkr.x3.trans hx3_1
  have hx4_4   : st4.regs.x4  = L.toUInt64 := hkr.x4.trans hx4_1
  have hx5_4   : st4.regs.x5  = L2.toUInt64 := hkr.x5.trans hx5_1
  have hx6_4   : st4.regs.x6  = L3.toUInt64 := hkr.x6.trans hx6_1
  have hx7_4   : st4.regs.x7  = L4.toUInt64 := hkr.x7.trans hx7_1
  have hx8_4   : st4.regs.x8  = objPtr := hkr.x8.trans hx8_1
  have hx9_4   : st4.regs.x9  = (uoff + L).toUInt64 := hkr.x9.trans hx9_1
  have hx10_4  : st4.regs.x10 = L5.toUInt64 := hkr.x10.trans hx10_1
  have hw11_4  : st4.getW r11 = s0v := hkr.w11.trans hw11_1
  have hw12_4  : st4.getW r12 = s1v := hkr.w12.trans hw12_1
  have hw13_4' : st4.getW r13 = s2v := hw13_4
  have ha0_4   : st4.regs.x15 = a0v := hx15_4.trans (hx15_3.trans hx15_2)
  have ha1_4   : st4.regs.x16 = a1v := hx16_4.trans (hx16_3.trans hx16_2)
  have hb0_4   : st4.regs.x17 = b0v := hx17_4.trans hx17_3
  have hb1_4   : st4.regs.x0  = b1v := hx0_4.trans hx0_3
  have hc0_4   : st4.regs.x19 = c0v := hx19_4
  have hc1_4   : st4.regs.x14 = c1v := hx14_4
  have u64_off : uoff.toUInt64 + 0x40 = (uoff + 64).toUInt64 := by
    have hus := usize_le_2pow64
    apply u64_ext
    rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64, hu64]
    change (uoff.toNat + 64) % 2 ^ 64 = uoff.toNat + 64
    exact Nat.mod_eq_of_lt (by omega)
  have da0 := StackDelta.refl hrw_args hcP hgP
  have wa0 := writeU64LE_sp_zero da0.rwRange L5.toUInt64
  have da1 := da0.step64_zero L5.toUInt64
  have wa1 := writeU32LE_sp_off da1.rwRange 0x0c s1v
  have da2 := da1.step32 0x0c s1v
  have wa2 := writeU32LE_sp_off da2.rwRange (0x0c + 4) s2v
  have da3 := da2.step32 (0x0c + 4) s2v
  have wa3 := writeU32LE_sp_off da3.rwRange 0x08 s0v
  have da4 := da3.step32 0x08 s0v
  have wa4 := writeU64LE_sp_off da4.rwRange 0x38 c0v
  have da5 := da4.step64 0x38 c0v
  have wa5 := writeU64LE_sp_off da5.rwRange (0x38 + 8) c1v
  have da6 := da5.step64 (0x38 + 8) c1v
  have wa6 := writeU64LE_sp_off da6.rwRange 0x28 b0v
  have da7 := da6.step64 0x28 b0v
  have wa7 := writeU64LE_sp_off da7.rwRange (0x28 + 8) b1v
  have da8 := da7.step64 (0x28 + 8) b1v
  have wa8 := writeU64LE_sp_off da8.rwRange 0x18 a0v
  have da9 := da8.step64 0x18 a0v
  have wa9 := writeU64LE_sp_off da9.rwRange (0x18 + 8) a1v
  have da10 := da9.step64 (0x18 + 8) a1v
  have hb_48 : sp0.toNat + 0x48 ≤ UInt64.size := da10.rwRange.1
  have stk_L5 : ((((((((((mPro.writeSlot64 sp0 L5.toUInt64).writeSlot32 (sp0 + 0x0c) s1v).writeSlot32
      (sp0 + (0x0c + 4)) s2v).writeSlot32 (sp0 + 0x08) s0v).writeSlot64 (sp0 + 0x38) c0v).writeSlot64
      (sp0 + (0x38 + 8)) c1v).writeSlot64 (sp0 + 0x28) b0v).writeSlot64 (sp0 + (0x28 + 8)) b1v).writeSlot64
      (sp0 + 0x18) a0v).writeSlot64 (sp0 + (0x18 + 8)) a1v).readU64LE sp0 = some L5.toUInt64 := by
    solve_slot_read hb_48
  rcases st4 with ⟨regs4, sp4, simd4, nzcv4, pc4, mem4⟩
  dsimp only at hpc4 hsp4 hm4 hx2_4 hx3_4 hx4_4 hx5_4 hx6_4 hx7_4 hx8_4 hx9_4 hx10_4
  dsimp only at hw11_4 hw12_4 hw13_4' ha0_4 ha1_4 hb0_4 hb1_4 hc0_4 hc1_4
  dsimp only [getW_mk_r11, getW_mk_r12, getW_mk_r13] at hw11_4 hw12_4 hw13_4'
  subst hpc4 hsp4 hm4
  have hb178 : BranchAt code (Layout.hwFold6Base + 712) Layout.hwFold6LoopBase true := by
    simpa [CodeLayout.symAddr] using
      da10.codeLoaded.hwFold6.2.1 { idx := 178, isCall := true, target := .fnHwFold6Loop } (by decide)
  f6_step_ex_with step_hwFold6 hcP 169 hwFold6Insn [hx10_4, wa0]
  f6_step_ex_with step_hwFold6 da1.codeLoaded 170 hwFold6Insn [hw12_4, hw13_4', wa1, wa2]
  f6_step_ex_with step_hwFold6 da3.codeLoaded 171 hwFold6Insn [hw11_4, wa3]
  f6_step_ex_with step_hwFold6 da4.codeLoaded 172 hwFold6Insn [hc0_4, hc1_4, wa4, wa5]
  f6_step_ex_with step_hwFold6 da6.codeLoaded 173 hwFold6Insn [hx2_4, u64_off]
  f6_step_ex_with step_hwFold6 da6.codeLoaded 174 hwFold6Insn [hb0_4, hb1_4, wa6, wa7]
  f6_step_ex_with step_hwFold6 da8.codeLoaded 175 hwFold6Insn [ha0_4, ha1_4, wa8, wa9]
  f6_step_ex_with step_hwFold6 da10.codeLoaded 176 hwFold6Insn [hx8_4]
  f6_step_ex_with step_hwFold6 da10.codeLoaded 177 hwFold6Insn [hx9_4]
  apply run_branch_call_at hb178
  dsimp only [setX_mk_r30]
  apply let_cur_state
  intro sCall
  have d_pre : StackDelta code Layout s.mem sCall.mem (s.sp - 0x100) 0x100 :=
    (d_full0.trans_sub d_pro (by omega) (by omega)).trans_sub da10 (by omega) (by omega)
  have hsub60 : sCall.sp - 0x60 = s.sp - 0x100 := sp_sub_0xa0_sub_0x60 s.sp
  have hrw_loop : sCall.mem.isRWRange (sCall.sp - 0x60) 0x60 := by
    rw [hsub60]
    exact isRWRange_sub d_pre.rwRange (by omega) (by omega)
  have hro_call : sCall.mem.hasROBytes (objPtr + 0x18) a := by
    rw [hbase]; exact d_pre.hasROBytes hro
  rcases hwFold6Loop_mc_spec (s := sCall) hs
      hle_loop hal_loop hL2 hL3 hL4 hL5 hLend
      da10.codeLoaded da10.globalsLoaded hro_call rfl
      (by dsimp only [sCall]; omega) hb_48 hrw_loop
      rfl rfl rfl hx3_4 hx4_4 hx5_4 hx6_4 hx7_4
      stk_L5
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48)
      (by dsimp only [sCall]; solve_slot_read hb_48) with
    ⟨kL, sRet, hrL, hpcRet, hr0Ret, d_loop, hcsRet⟩
  refine run_bind_exists hrL ?_
  have d_tot : StackDelta code Layout s.mem sRet.mem (s.sp - 0x100) 0x100 := by
    rw [hsub60] at d_loop
    exact d_pre.trans_sub d_loop (by omega) (by omega)
  have hsaved_call : SavedFrame6 sCall.mem sp0 s :=
    hsaved_pro.of_memOutsideEq da10.outside hb_a0 (by omega)
  have hsaved_ret : SavedFrame6 sRet.mem sp0 s := by
    rw [hsub60] at d_loop
    exact hsaved_call.of_memOutsideEq d_loop.outside hb_a0 (by omega)
  have hcRet := d_tot.codeLoaded
  have hpcRet' : sRet.pc = Layout.hwFold6Base + 716 :=
    hpcRet.trans (by dsimp only [sCall]; simp only [UInt64.add_assoc]; rfl)
  have hsp_ret  : sRet.sp = sp0 := hcsRet.sp
  have hx27_ret : sRet.regs.x27 = s.regs.x27 := hcsRet.x27.trans hkm.x27
  have hx28_ret : sRet.regs.x28 = s.regs.x28 := hcsRet.x28.trans hkm.x28
  have hd8_ret  : sRet.getD r8  = s.getD r8  := hcsRet.d8.trans hkm.d8
  have hd9_ret  : sRet.getD r9  = s.getD r9  := hcsRet.d9.trans hkm.d9
  have hd10_ret : sRet.getD r10 = s.getD r10 := hcsRet.d10.trans hkm.d10
  have hd11_ret : sRet.getD r11 = s.getD r11 := hcsRet.d11.trans hkm.d11
  have hd12_ret : sRet.getD r12 = s.getD r12 := hcsRet.d12.trans hkm.d12
  have hd13_ret : sRet.getD r13 = s.getD r13 := hcsRet.d13.trans hkm.d13
  have hd14_ret : sRet.getD r14 = s.getD r14 := hcsRet.d14.trans hkm.d14
  have hd15_ret : sRet.getD r15 = s.getD r15 := hcsRet.d15.trans hkm.d15
  have hsp_restore : sp0 + 0xa0 = s.sp := u64_sub_add_cancel s.sp 0xa0
  rcases sRet with ⟨regsR, spR, simdR, nzcvR, pcR, memR⟩
  dsimp only at hpcRet' hr0Ret hsp_ret hcRet hsaved_ret hx27_ret hx28_ret
  subst hpcRet' hsp_ret
  f6_step_ex_with step_hwFold6 hcRet 179 hwFold6Insn [hsaved_ret.sx29, hsaved_ret.sx30]
  f6_step_ex_with step_hwFold6 hcRet 180 hwFold6Insn [hsaved_ret.sx20, hsaved_ret.sx19]
  f6_step_ex_with step_hwFold6 hcRet 181 hwFold6Insn [hsaved_ret.sx22, hsaved_ret.sx21]
  f6_step_ex_with step_hwFold6 hcRet 182 hwFold6Insn [hsaved_ret.sx24, hsaved_ret.sx23]
  f6_step_ex_with step_hwFold6 hcRet 183 hwFold6Insn [hsaved_ret.sx26, hsaved_ret.sx25]
  f6_step_ex_with step_hwFold6 hcRet 184 hwFold6Insn [hsp_restore]
  f6_step_ex step_hwFold6 hcRet 185 hwFold6Insn
  refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, d_tot, ?_⟩
  · exact hr0Ret.trans hfold_eq
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hx27_ret, hx28_ret,
      rfl, rfl,
      hd8_ret, hd9_ret, hd10_ret, hd11_ret, hd12_ret, hd13_ret, hd14_ret, hd15_ret⟩

end Crc32c.Arm64MC
