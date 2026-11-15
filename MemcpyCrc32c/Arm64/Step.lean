/-
Shared symbolic-execution, byte-reassembly, and `rawExtend` absorption lemmas
for Phase 7 AArch64 machine-code verification (`MemcpyCrc32c.Arm64.*`).
-/
import MemcpyCrc32c.Arm64.Code
import MemcpyCrc32c.HwKernel

namespace Crc32c.Arm64MC
open SimdModels

/-! ### `UInt32` / `UInt16` bitwise OR AC instances for byte-reassembly (`ac_rfl`) -/

instance : Std.Associative (· ||| · : UInt32 → UInt32 → UInt32) where
  assoc a b c := by rw [← UInt32.toBitVec_inj]; simp [BitVec.or_assoc]

instance : Std.Commutative (· ||| · : UInt32 → UInt32 → UInt32) where
  comm a b := by rw [← UInt32.toBitVec_inj]; simp [BitVec.or_comm]

instance : Std.Associative (· ||| · : UInt16 → UInt16 → UInt16) where
  assoc a b c := by rw [← UInt16.toBitVec_inj]; simp [BitVec.or_assoc]

instance : Std.Commutative (· ||| · : UInt16 → UInt16 → UInt16) where
  comm a b := by rw [← UInt16.toBitVec_inj]; simp [BitVec.or_comm]

/-! ### Multi-step chaining helpers -/

theorem run_step {code : UInt64 → Option UInt32} {n : Nat} {s s1 s2 : Arm64.ArmState}
    (h1 : Arm64.step code s = some s1)
    (hn : Arm64.run code n s1 = some s2) :
    Arm64.run code (n + 1) s = some s2 := by
  rw [Arm64.run_succ, h1, Option.bind_some, hn]

theorem run_trans {code : UInt64 → Option UInt32} {m n : Nat} {s s1 s2 : Arm64.ArmState}
    (hm : Arm64.run code m s = some s1)
    (hn : Arm64.run code n s1 = some s2) :
    Arm64.run code (m + n) s = some s2 := by
  rw [Arm64.run_add, hm, Option.bind_some, hn]

theorem run_gotPair_step {code : UInt64 → Option UInt32} {n : Nat}
    {s s2 : Arm64.ArmState} {symAddr : UInt64} {rd : Arm64.RegIdx}
    (hg : Arm64.GotPairAt code s.mem s.pc symAddr rd)
    (hn : Arm64.run code n { (s.setX rd symAddr) with pc := s.pc + 8 } = some s2) :
    Arm64.run code (2 + n) s = some s2 :=
  run_trans (Arm64.run_gotPair hg) hn

theorem run_step_exists {code : UInt64 → Option UInt32} {s s1 : Arm64.ArmState}
    {P : Arm64.ArmState → Prop}
    (h1 : Arm64.step code s = some s1)
    (hrest : ∃ n s2, Arm64.run code n s1 = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  rcases hrest with ⟨n, s2, hn, hp⟩
  exact ⟨n + 1, s2, run_step h1 hn, hp⟩

theorem run_bind_exists {code : UInt64 → Option UInt32} {m : Nat} {s s1 : Arm64.ArmState}
    {P : Arm64.ArmState → Prop}
    (hm : Arm64.run code m s = some s1)
    (hrest : ∃ n s2, Arm64.run code n s1 = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 := by
  rcases hrest with ⟨n, s2, hn, hp⟩
  exact ⟨m + n, s2, run_trans hm hn, hp⟩

theorem run_gotPair_exists {code : UInt64 → Option UInt32}
    {s : Arm64.ArmState} {symAddr : UInt64} {rd : Arm64.RegIdx}
    {P : Arm64.ArmState → Prop}
    (hg : Arm64.GotPairAt code s.mem s.pc symAddr rd)
    (hrest : ∃ n s2, Arm64.run code n { (s.setX rd symAddr) with pc := s.pc + 8 } = some s2 ∧ P s2) :
    ∃ k s2, Arm64.run code k s = some s2 ∧ P s2 :=
  run_bind_exists (Arm64.run_gotPair hg) hrest

/-- Full AAPCS64 callee-saved register preservation (`SP`, `X19..X30`, and `D8..D15`). -/
structure CalleeSaved (s s' : Arm64.ArmState) : Prop where
  sp  : s'.sp = s.sp
  x19 : s'.regs.x19 = s.regs.x19
  x20 : s'.regs.x20 = s.regs.x20
  x21 : s'.regs.x21 = s.regs.x21
  x22 : s'.regs.x22 = s.regs.x22
  x23 : s'.regs.x23 = s.regs.x23
  x24 : s'.regs.x24 = s.regs.x24
  x25 : s'.regs.x25 = s.regs.x25
  x26 : s'.regs.x26 = s.regs.x26
  x27 : s'.regs.x27 = s.regs.x27
  x28 : s'.regs.x28 = s.regs.x28
  x29 : s'.regs.x29 = s.regs.x29
  x30 : s'.regs.x30 = s.regs.x30
  d8  : s'.getD r8 = s.getD r8
  d9  : s'.getD r9 = s.getD r9
  d10 : s'.getD r10 = s.getD r10
  d11 : s'.getD r11 = s.getD r11
  d12 : s'.getD r12 = s.getD r12
  d13 : s'.getD r13 = s.getD r13
  d14 : s'.getD r14 = s.getD r14
  d15 : s'.getD r15 = s.getD r15

theorem CalleeSaved.refl (s : Arm64.ArmState) : CalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CalleeSaved.trans {s1 s2 s3 : Arm64.ArmState}
    (h12 : CalleeSaved s1 s2) (h23 : CalleeSaved s2 s3) : CalleeSaved s1 s3 where
  sp  := h23.sp.trans h12.sp
  x19 := h23.x19.trans h12.x19
  x20 := h23.x20.trans h12.x20
  x21 := h23.x21.trans h12.x21
  x22 := h23.x22.trans h12.x22
  x23 := h23.x23.trans h12.x23
  x24 := h23.x24.trans h12.x24
  x25 := h23.x25.trans h12.x25
  x26 := h23.x26.trans h12.x26
  x27 := h23.x27.trans h12.x27
  x28 := h23.x28.trans h12.x28
  x29 := h23.x29.trans h12.x29
  x30 := h23.x30.trans h12.x30
  d8  := h23.d8.trans h12.d8
  d9  := h23.d9.trans h12.d9
  d10 := h23.d10.trans h12.d10
  d11 := h23.d11.trans h12.d11
  d12 := h23.d12.trans h12.d12
  d13 := h23.d13.trans h12.d13
  d14 := h23.d14.trans h12.d14
  d15 := h23.d15.trans h12.d15

/-! ### Width-cast, shift, bitwise, and model-alias `@[simp]` lemmas -/

@[simp] theorem toUInt32_toUInt64 (w : UInt32) : w.toUInt64.toUInt32 = w :=
  w.ofNat_toNat

@[simp] theorem toUInt8_toUInt32 (b : UInt8) : b.toUInt32.toUInt8 = b :=
  b.ofNat_toNat

@[simp] theorem toUInt16_toUInt32 (h : UInt16) : h.toUInt32.toUInt16 = h :=
  h.ofNat_toNat

@[simp] theorem zero_u64_toUInt32 : (0 : UInt64).toUInt32 = 0 := rfl

@[simp] theorem nat_toUInt64_zero : (0 : Nat).toUInt64 = 0 := rfl

@[simp] theorem mk_toBitVec_u64 (x : UInt64) : (⟨x.toBitVec⟩ : UInt64) = x := rfl

@[simp] theorem mk_toBitVec_u32 (x : UInt32) : (⟨x.toBitVec⟩ : UInt32) = x := rfl

@[simp] theorem ite_some_pc (c : Prop) [Decidable c]
    (regs : Arm64.RegFile) (sp : UInt64) (simd : Arm64.SimdFile)
    (nzcv : Arm64.PState) (p1 p2 : UInt64) (mem : Arm64.Mem) :
    (if c then some (Arm64.ArmState.mk regs sp simd nzcv p1 mem)
     else some (Arm64.ArmState.mk regs sp simd nzcv p2 mem)) =
      some (Arm64.ArmState.mk regs sp simd nzcv (if c then p1 else p2) mem) := by
  split <;> rfl

@[simp] theorem cond_c0_sub64 (x y : UInt64) (h : 0 < 16) :
    Arm64.conditionHolds ⟨0, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = (x == y) :=
  Arm64.conditionHolds_eq_sub64 x y

@[simp] theorem cond_c1_sub64 (x y : UInt64) (h : 1 < 16) :
    Arm64.conditionHolds ⟨1, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = (x != y) :=
  Arm64.conditionHolds_ne_sub64 x y

@[simp] theorem cond_c2_sub64 (x y : UInt64) (h : 2 < 16) :
    Arm64.conditionHolds ⟨2, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (y ≤ x) :=
  Arm64.conditionHolds_hs_sub64 x y

@[simp] theorem cond_c3_sub64 (x y : UInt64) (h : 3 < 16) :
    Arm64.conditionHolds ⟨3, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (x < y) :=
  Arm64.conditionHolds_lo_sub64 x y

@[simp] theorem cond_c8_sub64 (x y : UInt64) (h : 8 < 16) :
    Arm64.conditionHolds ⟨8, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (y < x) :=
  Arm64.conditionHolds_hi_sub64 x y

@[simp] theorem cond_c9_sub64 (x y : UInt64) (h : 9 < 16) :
    Arm64.conditionHolds ⟨9, h⟩ (Arm64.addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (x ≤ y) :=
  Arm64.conditionHolds_ls_sub64 x y

@[simp] theorem cond_c0_pstate (n z c v : Bool) (h : 0 < 16) :
    Arm64.conditionHolds ⟨0, h⟩ { n, z, c, v } = z :=
  Arm64.conditionHolds_eq_pstate n z c v

@[simp] theorem cond_c1_pstate (n z c v : Bool) (h : 1 < 16) :
    Arm64.conditionHolds ⟨1, h⟩ { n, z, c, v } = !z :=
  Arm64.conditionHolds_ne_pstate n z c v

@[simp] theorem movz64_zero : (0 : UInt16).toUInt64 <<< (0 : Nat).toUInt64 = 0 := rfl

@[simp] theorem movz32_zero : (0 : UInt16).toUInt32 <<< (0 : Nat).toUInt32 = 0 := rfl

@[simp] theorem logicOp_beq_ands_and : (Arm64.LogicOp.andOp == .andsOp) = false := rfl
@[simp] theorem logicOp_beq_ands_orr : (Arm64.LogicOp.orrOp == .andsOp) = false := rfl
@[simp] theorem logicOp_beq_ands_eor : (Arm64.LogicOp.eorOp == .andsOp) = false := rfl
@[simp] theorem logicOp_beq_ands_self : (Arm64.LogicOp.andsOp == .andsOp) = true := rfl

@[simp] theorem pairMode_post_post : (Arm64.PairMode.postIndex == .postIndex) = true := rfl
@[simp] theorem pairMode_signed_post : (Arm64.PairMode.signedOffset == .postIndex) = false := rfl
@[simp] theorem pairMode_pre_post : (Arm64.PairMode.preIndex == .postIndex) = false := rfl
@[simp] theorem pairMode_post_signed : (Arm64.PairMode.postIndex == .signedOffset) = false := rfl
@[simp] theorem pairMode_signed_signed : (Arm64.PairMode.signedOffset == .signedOffset) = true := rfl
@[simp] theorem pairMode_pre_signed : (Arm64.PairMode.preIndex == .signedOffset) = false := rfl

@[simp] theorem zero_or_u64 (x : UInt64) : (0 : UInt64) ||| x = x := by
  rw [← UInt64.toBitVec_inj]; simp

@[simp] theorem or_zero_u64 (x : UInt64) : x ||| (0 : UInt64) = x := by
  rw [← UInt64.toBitVec_inj]; simp

@[simp] theorem zero_or_u32 (x : UInt32) : (0 : UInt32) ||| x = x := by
  rw [← UInt32.toBitVec_inj]; simp

@[simp] theorem or_zero_u32 (x : UInt32) : x ||| (0 : UInt32) = x := by
  rw [← UInt32.toBitVec_inj]; simp

@[simp] theorem complement_u32_eq_xor (w : UInt32) : ~~~w = w ^^^ 0xFFFFFFFF := by
  rw [← UInt32.toBitVec_inj]
  ext i hi
  have h1 : ((0xFFFFFFFF : UInt32).toBitVec)[i] = true := by
    rw [BitVec.getElem_eq_testBit_toNat]
    change (2 ^ 32 - 1).testBit i = true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  simp only [UInt32.toBitVec_not, UInt32.toBitVec_xor, BitVec.getElem_not, BitVec.getElem_xor, h1]
  cases w.toBitVec[i] <;> rfl

@[simp] theorem shiftBV_lsl_zero {w : Nat} (x : BitVec w) :
    Arm64.shiftBV .lsl x 0 = x := by
  simp [Arm64.shiftBV]

@[simp] theorem shiftBV_lsl_u64 (x : UInt64) (amt : Nat) (h : amt < 64) :
    (⟨Arm64.shiftBV .lsl x.toBitVec amt⟩ : UInt64) = x <<< amt.toUInt64 := by
  rw [← UInt64.toBitVec_inj]
  have hmod : (amt.toUInt64.toBitVec % 64).toNat = amt := by
    rw [BitVec.toNat_umod]; change (amt % 2 ^ 64) % 64 = amt; omega
  change x.toBitVec <<< amt = x.toBitVec <<< (amt.toUInt64.toBitVec % 64)
  rw [BitVec.shiftLeft_eq', hmod]

@[simp] theorem shiftBV_lsl_u32 (x : UInt32) (amt : Nat) (h : amt < 32) :
    (⟨Arm64.shiftBV .lsl x.toBitVec amt⟩ : UInt32) = x <<< amt.toUInt32 := by
  rw [← UInt32.toBitVec_inj]
  have hmod : (amt.toUInt32.toBitVec % 32).toNat = amt := by
    rw [BitVec.toNat_umod]; change (amt % 2 ^ 32) % 32 = amt; omega
  change x.toBitVec <<< amt = x.toBitVec <<< (amt.toUInt32.toBitVec % 32)
  rw [BitVec.shiftLeft_eq', hmod]

@[simp] theorem shiftBV_lsr_u64 (x : UInt64) (amt : Nat) (h : amt < 64) :
    (⟨Arm64.shiftBV .lsr x.toBitVec amt⟩ : UInt64) = x >>> amt.toUInt64 := by
  rw [← UInt64.toBitVec_inj]
  have hmod : (amt.toUInt64.toBitVec % 64).toNat = amt := by
    rw [BitVec.toNat_umod]; change (amt % 2 ^ 64) % 64 = amt; omega
  change x.toBitVec >>> amt = x.toBitVec >>> (amt.toUInt64.toBitVec % 64)
  rw [BitVec.ushiftRight_eq', hmod]

@[simp] theorem shiftBV_lsr_u32 (x : UInt32) (amt : Nat) (h : amt < 32) :
    (⟨Arm64.shiftBV .lsr x.toBitVec amt⟩ : UInt32) = x >>> amt.toUInt32 := by
  rw [← UInt32.toBitVec_inj]
  have hmod : (amt.toUInt32.toBitVec % 32).toNat = amt := by
    rw [BitVec.toNat_umod]; change (amt % 2 ^ 32) % 32 = amt; omega
  change x.toBitVec >>> amt = x.toBitVec >>> (amt.toUInt32.toBitVec % 32)
  rw [BitVec.ushiftRight_eq', hmod]

@[simp] theorem toUInt16_reassemble2 (b0 b1 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8)).toUInt16 = word16 b0 b1 := by
  rw [← UInt16.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e32_16 : ∀ u : UInt32, u.toUInt16.toBitVec = u.toBitVec.setWidth 16 := fun _ => rfl
  have e8_32 : ∀ b : UInt8, b.toUInt32.toBitVec = b.toBitVec.setWidth 32 := fun _ => rfl
  have e8_16 : ∀ b : UInt8, b.toUInt16.toBitVec = b.toBitVec.setWidth 16 := fun _ => rfl
  have s32 : ∀ u : UInt32, (u <<< (8 : UInt32)).toBitVec = u.toBitVec <<< (8 : Nat) := fun _ => rfl
  have s16 : ∀ u : UInt16, (u <<< (8 : UInt16)).toBitVec = u.toBitVec <<< (8 : Nat) := fun _ => rfl
  unfold word16
  rw [e32_16, UInt32.toBitVec_or, UInt16.toBitVec_or, s32, s16, e8_32, e8_32, e8_16, e8_16]
  simp [hi]

@[simp] theorem toUInt16_reassemble2_comm (b0 b1 : UInt8) :
    ((b1.toUInt32 <<< 8) ||| b0.toUInt32).toUInt16 = word16 b0 b1 := by
  have hcomm : (b1.toUInt32 <<< 8) ||| b0.toUInt32 = b0.toUInt32 ||| (b1.toUInt32 <<< 8) := by
    ac_rfl
  rw [hcomm, toUInt16_reassemble2]

@[simp] theorem model_crc32c_u8 (c : UInt32) (v : UInt8) :
    Model.crc32c_u8 c v = SimdModels.crc32c_u8 c v := rfl

@[simp] theorem model_crc32c_u16 (c : UInt32) (v : UInt16) :
    Model.crc32c_u16 c v = SimdModels.crc32c_u16 c v := rfl

@[simp] theorem model_crc32c_u32 (c : UInt32) (v : UInt32) :
    Model.crc32c_u32 c v = SimdModels.crc32c_u32 c v := rfl

@[simp] theorem model_crc32c_u64 (c : UInt32) (v : UInt64) :
    Model.crc32c_u64 c v = SimdModels.crc32c_u64 c v := rfl

@[simp] theorem model_clmulLo (a b : UInt64) :
    Model.clmulLo a b = SimdModels.clmulLo a b := rfl

@[simp] theorem model_clmulHi (a b : UInt64) :
    Model.clmulHi a b = SimdModels.clmulHi a b := rfl

@[simp] theorem model_loadU8 (a : ByteArray) (i : USize) (h : i.toNat < a.size) :
    Model.loadU8 a i h = SimdModels.loadU8 a i h := rfl

@[simp] theorem model_loadU64LE (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) :
    Model.loadU64LE a i hs h = SimdModels.loadU64LE a i hs h := rfl

/-! ### `Nat`-indexed `rawExtend` byte / halfword / word / dword absorption lemmas -/

theorem rawExtend_u8_at (a : ByteArray) (off m : Nat) (h : off + 1 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a off (off + 1 + m)) =
      rawExtend (SimdModels.crc32c_u8 s (a[off]'(by omega))) (bytes a (off + 1) (off + 1 + m)) := by
  rw [crc32c_u8_eq, bytes_cons a off (off + 1 + m) (by omega) (by omega)]
  rfl

theorem rawExtend_u16_at (a : ByteArray) (hs : a.size < USize.size)
    (off m : Nat) (h : off + 2 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a off (off + 2 + m)) =
      rawExtend (SimdModels.crc32c_u16 s (word16 (a[off]'(by omega)) (a[off + 1]'(by omega))))
        (bytes a (off + 2) (off + 2 + m)) := by
  have hi : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
  have h1 : (off.toUSize + 1).toNat = off + 1 :=
    (usize_add_toNat off.toUSize 1 (by omega)).trans (by omega)
  have hload : load16 a off.toUSize hs (by omega) =
      word16 (a[off]'(by omega)) (a[off + 1]'(by omega)) := by
    unfold load16
    simp only [loadU8_eq_uget, uget_eq a off.toUSize off hi,
      uget_eq a (off.toUSize + 1) (off + 1) h1]
  rw [crc32c_u16_eq, ← hload]
  simpa [hi] using rawExtend_load16 a off.toUSize hs m (by omega) s

theorem rawExtend_u32_at (a : ByteArray) (hs : a.size < USize.size)
    (off m : Nat) (h : off + 4 + m ≤ a.size) (s : UInt32) :
    rawExtend s (bytes a off (off + 4 + m)) =
      rawExtend (SimdModels.crc32c_u32 s
          (word32 (a[off]'(by omega)) (a[off + 1]'(by omega))
            (a[off + 2]'(by omega)) (a[off + 3]'(by omega))))
        (bytes a (off + 4) (off + 4 + m)) := by
  have hi : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
  have h1 : (off.toUSize + 1).toNat = off + 1 :=
    (usize_add_toNat off.toUSize 1 (by omega)).trans (by omega)
  have h2 : (off.toUSize + 2).toNat = off + 2 :=
    (usize_add_toNat off.toUSize 2 (by omega)).trans (by omega)
  have h3 : (off.toUSize + 3).toNat = off + 3 :=
    (usize_add_toNat off.toUSize 3 (by omega)).trans (by omega)
  have hload : load32 a off.toUSize hs (by omega) =
      word32 (a[off]'(by omega)) (a[off + 1]'(by omega))
        (a[off + 2]'(by omega)) (a[off + 3]'(by omega)) := by
    unfold load32
    simp only [loadU8_eq_uget,
      uget_eq a off.toUSize off hi,
      uget_eq a (off.toUSize + 1) (off + 1) h1,
      uget_eq a (off.toUSize + 2) (off + 2) h2,
      uget_eq a (off.toUSize + 3) (off + 3) h3]
  rw [crc32c_u32_eq, ← hload]
  simpa [hi] using rawExtend_load32 a off.toUSize hs m (by omega) s

theorem hasROBytes_readU64LE_nat {m : Arm64.Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (hs : bs.size < USize.size)
    (off : Nat) (hoff : off + 8 ≤ bs.size) :
    have _ : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    m.readU64LE (base + off.toUInt64) =
      some (SimdModels.loadU64LE bs off.toUSize hs (by omega)) := by
  intro hi
  have hus : USize.size ≤ 2 ^ 64 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [USize.size, h]
  have hoff64 : off < 2 ^ 64 := by omega
  have heq : off.toUInt64 = off.toUSize.toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change off.toUInt64.toNat = off.toUSize.toUInt64.toNat
    rw [USize.toNat_toUInt64, hi]
    simp [Nat.toUInt64]
    omega
  rw [heq]
  exact Arm64.Mem.hasROBytes_readU64LE hro hs off.toUSize (by omega)

theorem rawExtend_u64_at (a : ByteArray) (hs : a.size < USize.size)
    (off m : Nat) (h : off + 8 + m ≤ a.size) (s : UInt32) :
    have _ : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    rawExtend s (bytes a off (off + 8 + m)) =
      rawExtend (SimdModels.crc32c_u64 s (SimdModels.loadU64LE a off.toUSize hs (by omega)))
        (bytes a (off + 8) (off + 8 + m)) := by
  intro hi
  rw [crc32c_u64_eq, loadU64LE_eq_load64]
  simpa [hi] using rawExtend_load a off.toUSize hs m (by omega) s

/-! ### Reusable straight-line instruction stepping tactic -/

/-- Execute one unrelocated instruction `idx` via `step_thm hc idx`, reducing the
post-state to flat structure form on the LHS before binding the next state via `rfl`. -/
macro "mc_step" step_thm:ident hc:ident idx:num insn_fn:ident : tactic =>
  `(tactic| (
      apply run_step
      · rw [$step_thm $hc $idx _ (by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)]
        conv_lhs =>
          simp only [$insn_fn:ident, ↓reduceIte, Nat.reduceLT]
          simp only [↓reduceIte,
            Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceBEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff,
            Bool.false_eq_true, Bool.not_true, Bool.not_false,
            r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
            r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, l0, l1,
            logicOp_beq_ands_and, logicOp_beq_ands_orr, logicOp_beq_ands_eor, logicOp_beq_ands_self,
            pairMode_post_post, pairMode_signed_post, pairMode_pre_post,
            pairMode_post_signed, pairMode_signed_signed, pairMode_pre_signed,
            Arm64.execInstr,
            Arm64.ArmState.getX, Arm64.ArmState.getW, Arm64.ArmState.setX, Arm64.ArmState.setW,
            Arm64.ArmState.getXSP, Arm64.ArmState.getWSP, Arm64.ArmState.setXSP, Arm64.ArmState.setWSP,
            Arm64.ArmState.getV, Arm64.ArmState.setV, Arm64.ArmState.getD, Arm64.ArmState.setD,
            Arm64.ArmState.nextPC,
            Arm64.RegFile.get, Arm64.RegFile.set, Arm64.SimdFile.get, Arm64.SimdFile.set,
            Option.bind_eq_bind, Option.bind,
            UInt64.add_assoc, UInt64.add_zero,
            Arm64.lo64_ofHalves_simp, Arm64.hi64_ofHalves_simp,
            Arm64.lane64_zero_simp, Arm64.lane64_one_simp,
            Arm64.veorq_ofHalves, Arm64.veor8b_ofHalves, Arm64.veor3q_ofHalves,
            Arm64.zip2_2d_ofHalves, Arm64.insLane64_zero_ofHalves, Arm64.insLane64_one_ofHalves,
            Arm64.vextq_8_ofHalves, Arm64.vmull_p64_ofHalves,
            Arm64.addWithCarry_sub64_fst,
            cond_c0_sub64, cond_c1_sub64, cond_c2_sub64, cond_c3_sub64,
            cond_c8_sub64, cond_c9_sub64, cond_c0_pstate, cond_c1_pstate,
            ite_some_pc, decide_eq_true_eq,
            Arm64.conditionHolds_eq_sub64, Arm64.conditionHolds_ne_sub64,
            Arm64.conditionHolds_hs_sub64, Arm64.conditionHolds_lo_sub64,
            Arm64.conditionHolds_hi_sub64, Arm64.conditionHolds_ls_sub64,
            Arm64.conditionHolds_eq_pstate, Arm64.conditionHolds_ne_pstate,
            Arm64.evalUbfm_lsr64, Arm64.evalUbfm_lsr32,
            Arm64.evalUbfm_lsl64, Arm64.evalUbfm_ubfiz32_64,
            mk_toBitVec_u64, mk_toBitVec_u32,
            toUInt32_toUInt64, toUInt8_toUInt32, toUInt16_toUInt32,
            zero_u64_toUInt32, movz64_zero, movz32_zero,
            zero_or_u64, or_zero_u64, zero_or_u32, or_zero_u32,
            complement_u32_eq_xor,
            shiftBV_lsl_zero, shiftBV_lsl_u64, shiftBV_lsl_u32,
            shiftBV_lsr_u64, shiftBV_lsr_u32,
            toUInt16_reassemble2, toUInt16_reassemble2_comm,
            model_crc32c_u8, model_crc32c_u16, model_crc32c_u32, model_crc32c_u64,
            model_clmulLo, model_clmulHi, model_loadU8, model_loadU64LE]
    ))

/-- Same as `mc_step`, accepting extra local memory/branch hypotheses for `simp`. -/
macro "mc_step_with" step_thm:ident hc:ident idx:num insn_fn:ident
    "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
      apply run_step
      · rw [$step_thm $hc $idx _ (by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)]
        conv_lhs =>
          simp only [$insn_fn:ident, ↓reduceIte, Nat.reduceLT]
          simp only [↓reduceIte,
            Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceBEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff,
            Bool.false_eq_true, Bool.not_true, Bool.not_false,
            r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
            r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, l0, l1,
            logicOp_beq_ands_and, logicOp_beq_ands_orr, logicOp_beq_ands_eor, logicOp_beq_ands_self,
            pairMode_post_post, pairMode_signed_post, pairMode_pre_post,
            pairMode_post_signed, pairMode_signed_signed, pairMode_pre_signed,
            Arm64.execInstr,
            Arm64.ArmState.getX, Arm64.ArmState.getW, Arm64.ArmState.setX, Arm64.ArmState.setW,
            Arm64.ArmState.getXSP, Arm64.ArmState.getWSP, Arm64.ArmState.setXSP, Arm64.ArmState.setWSP,
            Arm64.ArmState.getV, Arm64.ArmState.setV, Arm64.ArmState.getD, Arm64.ArmState.setD,
            Arm64.ArmState.nextPC,
            Arm64.RegFile.get, Arm64.RegFile.set, Arm64.SimdFile.get, Arm64.SimdFile.set,
            Option.bind_eq_bind, Option.bind,
            UInt64.add_assoc, UInt64.add_zero,
            Arm64.lo64_ofHalves_simp, Arm64.hi64_ofHalves_simp,
            Arm64.lane64_zero_simp, Arm64.lane64_one_simp,
            Arm64.veorq_ofHalves, Arm64.veor8b_ofHalves, Arm64.veor3q_ofHalves,
            Arm64.zip2_2d_ofHalves, Arm64.insLane64_zero_ofHalves, Arm64.insLane64_one_ofHalves,
            Arm64.vextq_8_ofHalves, Arm64.vmull_p64_ofHalves,
            Arm64.addWithCarry_sub64_fst,
            cond_c0_sub64, cond_c1_sub64, cond_c2_sub64, cond_c3_sub64,
            cond_c8_sub64, cond_c9_sub64, cond_c0_pstate, cond_c1_pstate,
            ite_some_pc, decide_eq_true_eq,
            Arm64.conditionHolds_eq_sub64, Arm64.conditionHolds_ne_sub64,
            Arm64.conditionHolds_hs_sub64, Arm64.conditionHolds_lo_sub64,
            Arm64.conditionHolds_hi_sub64, Arm64.conditionHolds_ls_sub64,
            Arm64.conditionHolds_eq_pstate, Arm64.conditionHolds_ne_pstate,
            Arm64.evalUbfm_lsr64, Arm64.evalUbfm_lsr32,
            Arm64.evalUbfm_lsl64, Arm64.evalUbfm_ubfiz32_64,
            mk_toBitVec_u64, mk_toBitVec_u32,
            toUInt32_toUInt64, toUInt8_toUInt32, toUInt16_toUInt32,
            zero_u64_toUInt32, movz64_zero, movz32_zero,
            zero_or_u64, or_zero_u64, zero_or_u32, or_zero_u32,
            complement_u32_eq_xor,
            shiftBV_lsl_zero, shiftBV_lsl_u64, shiftBV_lsl_u32,
            shiftBV_lsr_u64, shiftBV_lsr_u32,
            toUInt16_reassemble2, toUInt16_reassemble2_comm,
            model_crc32c_u8, model_crc32c_u16, model_crc32c_u32, model_crc32c_u64,
            model_clmulLo, model_clmulHi, model_loadU8, model_loadU64LE,
            $extras,*]
    ))

/-- Existential-step variant of `mc_step` for goals `∃ k s', Arm64.run code k s = some s' ∧ P s'`. -/
macro "mc_step_ex" step_thm:ident hc:ident idx:num insn_fn:ident : tactic =>
  `(tactic| (
      apply run_step_exists
      · rw [$step_thm $hc $idx _ (by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)]
        conv_lhs =>
          simp only [$insn_fn:ident, ↓reduceIte, Nat.reduceLT]
          simp only [↓reduceIte,
            Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceBEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff,
            Bool.false_eq_true, Bool.not_true, Bool.not_false,
            r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
            r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, l0, l1,
            logicOp_beq_ands_and, logicOp_beq_ands_orr, logicOp_beq_ands_eor, logicOp_beq_ands_self,
            pairMode_post_post, pairMode_signed_post, pairMode_pre_post,
            pairMode_post_signed, pairMode_signed_signed, pairMode_pre_signed,
            Arm64.execInstr,
            Arm64.ArmState.getX, Arm64.ArmState.getW, Arm64.ArmState.setX, Arm64.ArmState.setW,
            Arm64.ArmState.getXSP, Arm64.ArmState.getWSP, Arm64.ArmState.setXSP, Arm64.ArmState.setWSP,
            Arm64.ArmState.getV, Arm64.ArmState.setV, Arm64.ArmState.getD, Arm64.ArmState.setD,
            Arm64.ArmState.nextPC,
            Arm64.RegFile.get, Arm64.RegFile.set, Arm64.SimdFile.get, Arm64.SimdFile.set,
            Option.bind_eq_bind, Option.bind,
            UInt64.add_assoc, UInt64.add_zero,
            Arm64.lo64_ofHalves_simp, Arm64.hi64_ofHalves_simp,
            Arm64.lane64_zero_simp, Arm64.lane64_one_simp,
            Arm64.veorq_ofHalves, Arm64.veor8b_ofHalves, Arm64.veor3q_ofHalves,
            Arm64.zip2_2d_ofHalves, Arm64.insLane64_zero_ofHalves, Arm64.insLane64_one_ofHalves,
            Arm64.vextq_8_ofHalves, Arm64.vmull_p64_ofHalves,
            Arm64.addWithCarry_sub64_fst,
            cond_c0_sub64, cond_c1_sub64, cond_c2_sub64, cond_c3_sub64,
            cond_c8_sub64, cond_c9_sub64, cond_c0_pstate, cond_c1_pstate,
            ite_some_pc, decide_eq_true_eq,
            Arm64.conditionHolds_eq_sub64, Arm64.conditionHolds_ne_sub64,
            Arm64.conditionHolds_hs_sub64, Arm64.conditionHolds_lo_sub64,
            Arm64.conditionHolds_hi_sub64, Arm64.conditionHolds_ls_sub64,
            Arm64.conditionHolds_eq_pstate, Arm64.conditionHolds_ne_pstate,
            Arm64.evalUbfm_lsr64, Arm64.evalUbfm_lsr32,
            Arm64.evalUbfm_lsl64, Arm64.evalUbfm_ubfiz32_64,
            mk_toBitVec_u64, mk_toBitVec_u32,
            toUInt32_toUInt64, toUInt8_toUInt32, toUInt16_toUInt32,
            zero_u64_toUInt32, movz64_zero, movz32_zero,
            zero_or_u64, or_zero_u64, zero_or_u32, or_zero_u32,
            complement_u32_eq_xor,
            shiftBV_lsl_zero, shiftBV_lsl_u64, shiftBV_lsl_u32,
            shiftBV_lsr_u64, shiftBV_lsr_u32,
            toUInt16_reassemble2, toUInt16_reassemble2_comm,
            model_crc32c_u8, model_crc32c_u16, model_crc32c_u32, model_crc32c_u64,
            model_clmulLo, model_clmulHi, model_loadU8, model_loadU64LE]
    ))

/-- Existential-step variant of `mc_step_with`. -/
macro "mc_step_ex_with" step_thm:ident hc:ident idx:num insn_fn:ident
    "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
      apply run_step_exists
      · rw [$step_thm $hc $idx _ (by simp only [Nat.mul_zero, nat_toUInt64_zero, UInt64.add_assoc, UInt64.add_zero]; try rfl)]
        conv_lhs =>
          simp only [$insn_fn:ident, ↓reduceIte, Nat.reduceLT]
          simp only [↓reduceIte,
            Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceBEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff,
            Bool.false_eq_true, Bool.not_true, Bool.not_false,
            r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
            r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, l0, l1,
            logicOp_beq_ands_and, logicOp_beq_ands_orr, logicOp_beq_ands_eor, logicOp_beq_ands_self,
            pairMode_post_post, pairMode_signed_post, pairMode_pre_post,
            pairMode_post_signed, pairMode_signed_signed, pairMode_pre_signed,
            Arm64.execInstr,
            Arm64.ArmState.getX, Arm64.ArmState.getW, Arm64.ArmState.setX, Arm64.ArmState.setW,
            Arm64.ArmState.getXSP, Arm64.ArmState.getWSP, Arm64.ArmState.setXSP, Arm64.ArmState.setWSP,
            Arm64.ArmState.getV, Arm64.ArmState.setV, Arm64.ArmState.getD, Arm64.ArmState.setD,
            Arm64.ArmState.nextPC,
            Arm64.RegFile.get, Arm64.RegFile.set, Arm64.SimdFile.get, Arm64.SimdFile.set,
            Option.bind_eq_bind, Option.bind,
            UInt64.add_assoc, UInt64.add_zero,
            Arm64.lo64_ofHalves_simp, Arm64.hi64_ofHalves_simp,
            Arm64.lane64_zero_simp, Arm64.lane64_one_simp,
            Arm64.veorq_ofHalves, Arm64.veor8b_ofHalves, Arm64.veor3q_ofHalves,
            Arm64.zip2_2d_ofHalves, Arm64.insLane64_zero_ofHalves, Arm64.insLane64_one_ofHalves,
            Arm64.vextq_8_ofHalves, Arm64.vmull_p64_ofHalves,
            Arm64.addWithCarry_sub64_fst,
            cond_c0_sub64, cond_c1_sub64, cond_c2_sub64, cond_c3_sub64,
            cond_c8_sub64, cond_c9_sub64, cond_c0_pstate, cond_c1_pstate,
            ite_some_pc, decide_eq_true_eq,
            Arm64.conditionHolds_eq_sub64, Arm64.conditionHolds_ne_sub64,
            Arm64.conditionHolds_hs_sub64, Arm64.conditionHolds_lo_sub64,
            Arm64.conditionHolds_hi_sub64, Arm64.conditionHolds_ls_sub64,
            Arm64.conditionHolds_eq_pstate, Arm64.conditionHolds_ne_pstate,
            Arm64.evalUbfm_lsr64, Arm64.evalUbfm_lsr32,
            Arm64.evalUbfm_lsl64, Arm64.evalUbfm_ubfiz32_64,
            mk_toBitVec_u64, mk_toBitVec_u32,
            toUInt32_toUInt64, toUInt8_toUInt32, toUInt16_toUInt32,
            zero_u64_toUInt32, movz64_zero, movz32_zero,
            zero_or_u64, or_zero_u64, zero_or_u32, or_zero_u32,
            complement_u32_eq_xor,
            shiftBV_lsl_zero, shiftBV_lsl_u64, shiftBV_lsl_u32,
            shiftBV_lsr_u64, shiftBV_lsr_u32,
            toUInt16_reassemble2, toUInt16_reassemble2_comm,
            model_crc32c_u8, model_crc32c_u16, model_crc32c_u32, model_crc32c_u64,
            model_clmulLo, model_clmulHi, model_loadU8, model_loadU64LE,
            $extras,*]
    ))

end Crc32c.Arm64MC
