/-
Machine-code verification of `_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg`
(`119` instructions, `Hw.c.o`) against `Crc32c.rawExtendHwMulti` and
`Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + ulen.toNat))`.

Covers:
- `0x50`-byte stack frame prologue/epilogue (`[s.sp - 0x50, s.sp)`), nested cleanly
  above `hwFold6`'s `0x100`-byte frame (`[s.sp - 0x150, s.sp - 0x50)`).
- Compiler-synthesized reciprocal-multiply unsigned divisions by `48` (`0xaaab >>> 21`
  on `< 768` and `umulh 0xaaaaaaaaaaaaaaab >>> 5` on `< 384`) and by `384`
  (`umulh 0xaaaaaaaaaaaaaaab >>> 8` on `< 2^64`), proved by pure `Nat` arithmetic.
- Both inlined `hwFold3` (`48 B/iter`, `3 × CRC32CX`) loops (`idx 29..44` and
  `idx 88..103`), calls to `hwFold6` and `combine3`, and tail jump to `hwLoop`.
Kernel-checked without `bv_decide`.
-/
import MemcpyCrc32c.Arm64.HwFold6

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Section 1: Reciprocal-multiply division, shift, and pointer arithmetic lemmas -/

theorem sp_pre_0x50 (sp : UInt64) : sp + 0xffffffffffffffb0 = sp - 0x50 := by
  rw [← UInt64.toBitVec_inj]
  change sp.toBitVec + 0xffffffffffffffb0#64 = sp.toBitVec - 0x50#64
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem u64_add_sub_cancel (a b : UInt64) : (a + b) - b = a := by
  rw [← UInt64.toBitVec_inj]
  simp

theorem sp_sub_0x50_sub_0x100 (sp : UInt64) : (sp - 0x50) - 0x100 = sp - 0x150 := by
  have h1 : (0x150 : UInt64) = 0x100 + 0x50 := rfl
  have h2 : sp - 0x50 = (sp - 0x150) + 0x100 := by
    calc sp - 0x50
      _ = ((sp - 0x150) + 0x150) - 0x50 := by rw [u64_sub_add_cancel]
      _ = (((sp - 0x150) + 0x100) + 0x50) - 0x50 := by rw [h1, ← UInt64.add_assoc]
      _ = (sp - 0x150) + 0x100 := u64_add_sub_cancel _ _
  rw [h2, u64_add_sub_cancel]

private theorem and_ffff_lt768 (ulen : USize) (hlt : ulen.toNat < 768) :
    ulen.toUInt64.toUInt32 &&& (0xffff : UInt64).toUInt32 = ulen.toUInt64.toUInt32 := by
  have hus := usize_le_2pow64
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (ulen.toUInt64.toNat % 2 ^ 32) &&& 65535 = ulen.toUInt64.toNat % 2 ^ 32
  rw [USize.toNat_toUInt64]
  have h1 : (65535 : Nat) = 2 ^ 16 - 1 := rfl
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem movz32_aaab : (0xaaab : UInt16).toUInt32 <<< (0 : Nat).toUInt32 = 0xaaab := rfl

private theorem magic_div_eq (n d m s k : Nat)
    (_hd : 0 < d) (hs : 0 < s)
    (hid : d * m = s + k)
    (hbound : k * (n / d) + (n % d) * m < s) :
    (n * m) / s = n / d := by
  let q := n / d
  let r := n % d
  have hn : n = d * q + r := (Nat.div_add_mod n d).symm
  have hdecomp : n * m = s * q + (k * q + r * m) := by
    calc n * m
      _ = (d * q + r) * m := by rw [← hn]
      _ = d * q * m + r * m := Nat.add_mul (d * q) r m
      _ = (d * m) * q + r * m := by rw [Nat.mul_right_comm d q m]
      _ = (s + k) * q + r * m := by rw [hid]
      _ = (s * q + k * q) + r * m := by rw [Nat.add_mul s k q]
      _ = s * q + (k * q + r * m) := Nat.add_assoc (s * q) (k * q) (r * m)
  rw [hdecomp, Nat.mul_add_div hs q (k * q + r * m), Nat.div_eq_of_lt hbound, Nat.add_zero]

private theorem magic_div_bounded (n nMax d m s k : Nat)
    (hn : n ≤ nMax)
    (hd : 0 < d) (hs : 0 < s)
    (hid : d * m = s + k)
    (hmax : k * (nMax / d) + (d - 1) * m < s) :
    (n * m) / s = n / d := by
  have hq : n / d ≤ nMax / d := Nat.div_le_div_right hn
  have hr : n % d ≤ d - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt n hd)
  have hb : k * (n / d) + (n % d) * m < s :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_left k hq) (Nat.mul_le_mul_right m hr)) hmax
  exact magic_div_eq n d m s k hd hs hid hb

private theorem div48_u32_magic (ulen : USize) (hlt : ulen.toNat < 768) :
    ((ulen.toUInt64.toUInt32 * 0xaaab) >>> (21 : Nat).toUInt32).toUInt64 = (ulen / 48).toUInt64 := by
  have hus := usize_le_2pow64
  apply u64_ext
  have e48 : (48 : USize).toNat = 48 := by simp
  rw [UInt32.toNat_toUInt64, UInt32.toNat_shiftRight, UInt32.toNat_mul,
    UInt64.toNat_toUInt32, USize.toNat_toUInt64, USize.toNat_toUInt64,
    USize.toNat_div, e48]
  have hm : (0xaaab : UInt32).toNat = 43691 := rfl
  have hs : ((21 : Nat).toUInt32).toNat % 32 = 21 := rfl
  rw [hm, hs, Nat.shiftRight_eq_div_pow]
  have hn_le : ulen.toNat ≤ 767 := Nat.le_sub_one_of_lt hlt
  have hlt_u32 : ulen.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt hn_le (by decide)
  rw [Nat.mod_eq_of_lt hlt_u32]
  have hlt32 : ulen.toNat * 43691 < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 43691 hn_le) (by decide)
  rw [Nat.mod_eq_of_lt hlt32]
  exact magic_div_bounded ulen.toNat 767 48 43691 (2 ^ 21) 16 hn_le
    (by decide) (by decide) rfl (by decide)

private theorem movk_magic_aaab :
    ((0xaaaaaaaaaaaaaaaa : UInt64) &&& ~~~((0xFFFF : UInt64) <<< (0 : Nat).toUInt64)) |||
      ((0xaaab : UInt16).toUInt64 <<< (0 : Nat).toUInt64) = 0xaaaaaaaaaaaaaaab := rfl

private theorem umulh_div384 (ulen : USize) :
    (UInt64.ofNat ((ulen.toUInt64.toNat * (0xaaaaaaaaaaaaaaab : UInt64).toNat) >>> 64)) >>>
      (8 : Nat).toUInt64 = (ulen / 384).toUInt64 := by
  have hus := usize_le_2pow64
  have hn : ulen.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size ulen) hus
  have hn_le : ulen.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hn
  have hm : (0xaaaaaaaaaaaaaaab : UInt64).toNat = 12297829382473034411 := rfl
  apply u64_ext
  have e384 : (384 : USize).toNat = 384 := by simp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', USize.toNat_toUInt64,
    USize.toNat_toUInt64, USize.toNat_div, e384, hm]
  have hs8 : ((8 : Nat).toUInt64).toNat % 64 = 8 := rfl
  rw [hs8, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hprod_lt : (ulen.toNat * 12297829382473034411) / 2 ^ 64 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt
      (Nat.div_le_div_right (Nat.mul_le_mul_right 12297829382473034411 hn_le))
      (by decide)
  rw [Nat.mod_eq_of_lt hprod_lt, Nat.div_div_eq_div_mul]
  exact magic_div_bounded ulen.toNat (2 ^ 64 - 1) 384 12297829382473034411
    (2 ^ 64 * 2 ^ 8) 128 hn_le (by decide) (by decide) rfl (by decide)

private theorem umulh_div48 (rem : USize) (hlt : rem.toNat < 384) :
    (UInt64.ofNat ((rem.toUInt64.toNat * (0xaaaaaaaaaaaaaaab : UInt64).toNat) >>> 64)) >>>
      (5 : Nat).toUInt64 = (rem / 48).toUInt64 := by
  have hn_le : rem.toNat ≤ 383 := Nat.le_sub_one_of_lt hlt
  have hm : (0xaaaaaaaaaaaaaaab : UInt64).toNat = 12297829382473034411 := rfl
  apply u64_ext
  have e48 : (48 : USize).toNat = 48 := by simp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', USize.toNat_toUInt64,
    USize.toNat_toUInt64, USize.toNat_div, e48, hm]
  have hs5 : ((5 : Nat).toUInt64).toNat % 64 = 5 := rfl
  rw [hs5, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hprod_lt : (rem.toNat * 12297829382473034411) / 2 ^ 64 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt
      (Nat.div_le_div_right (Nat.mul_le_mul_right 12297829382473034411 hn_le))
      (by decide)
  rw [Nat.mod_eq_of_lt hprod_lt, Nat.div_div_eq_div_mul]
  exact magic_div_bounded rem.toNat 383 48 12297829382473034411
    (2 ^ 64 * 2 ^ 5) 16 hn_le (by decide) (by decide) rfl (by decide)

private theorem ubfiz_shl (b res : USize) (sh : Nat) (hsh : sh < 32)
    (hb : b.toNat < 2 ^ 32) (hres : res.toNat = b.toNat * 2 ^ sh) :
    b.toUInt64.toUInt32.toUInt64 <<< sh.toUInt64 = res.toUInt64 := by
  have hus := usize_le_2pow64
  have hres64 : res.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size res) hus
  apply u64_ext
  rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32,
    USize.toNat_toUInt64, USize.toNat_toUInt64, Nat.mod_eq_of_lt hb]
  have hmod : sh.toUInt64.toNat % 64 = sh := by
    rw [nat_toUInt64_toNat sh (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod, Nat.shiftLeft_eq, ← hres, Nat.mod_eq_of_lt hres64]

private theorem lsl64_usize (b res : USize) (sh : Nat) (hsh : sh < 64)
    (hres : res.toNat = b.toNat * 2 ^ sh) :
    b.toUInt64 <<< sh.toUInt64 = res.toUInt64 := by
  have hus := usize_le_2pow64
  have hres64 : res.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size res) hus
  apply u64_ext
  rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64]
  have hmod : sh.toUInt64.toNat % 64 = sh := by
    rw [nat_toUInt64_toNat sh (by omega), Nat.mod_eq_of_lt hsh]
  rw [hmod, Nat.shiftLeft_eq, ← hres, Nat.mod_eq_of_lt hres64]

private theorem usize_add_u64 {x y z : USize} (h : z.toNat = x.toNat + y.toNat) :
    x.toUInt64 + y.toUInt64 = z.toUInt64 := by
  have hus := usize_le_2pow64
  have hz : z.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size z) hus
  apply u64_ext
  rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64, USize.toNat_toUInt64,
    ← h, Nat.mod_eq_of_lt hz]

private theorem usize_sub_u64 {x y z : USize} (hle : y.toNat ≤ x.toNat)
    (h : z.toNat = x.toNat - y.toNat) :
    x.toUInt64 - y.toUInt64 = z.toUInt64 := by
  apply u64_ext
  have hle64 : y.toUInt64 ≤ x.toUInt64 := by
    change y.toUInt64.toNat ≤ x.toUInt64.toNat
    rw [USize.toNat_toUInt64, USize.toNat_toUInt64]; exact hle
  rw [UInt64.toNat_sub_of_le _ _ hle64, USize.toNat_toUInt64, USize.toNat_toUInt64,
    USize.toNat_toUInt64, h]

private theorem usize_add_lit_u64 {x : USize} {c : UInt64} {z : USize}
    (h : z.toNat = x.toNat + c.toNat) :
    x.toUInt64 + c = z.toUInt64 := by
  have hus := usize_le_2pow64
  have hz : z.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size z) hus
  apply u64_ext
  rw [UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64,
    ← h, Nat.mod_eq_of_lt hz]

private theorem usize_add8_toNat (p : USize) (hp : p.toNat + 8 < USize.size) :
    (p + 8).toNat = p.toNat + 8 := by
  have e8 : (8 : USize).toNat = 8 := by simp
  rw [USize.toNat_add, e8]
  exact Nat.mod_eq_of_lt hp

private theorem usize_add16_toNat (p : USize) (hp : p.toNat + 16 < USize.size) :
    (p + 16).toNat = p.toNat + 16 := by
  have e16 : (16 : USize).toNat = 16 := by simp
  rw [USize.toNat_add, e16]
  exact Nat.mod_eq_of_lt hp

/-! ### Section 2: 16-byte `.ro` block read helper (`crc128`) & `0x50` saved-frame bundle -/

private structure Block128Reads (m : Arm64.Mem) (base : UInt64) (a : ByteArray)
    (hs : a.size < USize.size) (p : USize) (hp : p.toNat + 16 ≤ a.size) : Prop where
  r0 : m.readU64LE (base + p.toUInt64) = some (SimdModels.loadU64LE a p hs (by omega))
  r1 : m.readU64LE (base + (p.toUInt64 + 8)) =
       some (SimdModels.loadU64LE a (p + 8) hs
         (by have := usize_add8_toNat p (by omega); omega))

private theorem block128Reads_of_ro {m : Arm64.Mem} {base : UInt64} {a : ByteArray}
    (hro : m.hasROBytes base a) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 16 ≤ a.size) : Block128Reads m base a hs p hp := by
  have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add8_toNat p (by omega)
  have hadd8 : base + (p.toUInt64 + 8) = base + (p + 8).toUInt64 := by
    congr 1; exact usize_add_lit_u64 hp8
  refine ⟨Arm64.Mem.hasROBytes_readU64LE hro hs p (by omega), ?_⟩
  rw [hadd8]
  exact Arm64.Mem.hasROBytes_readU64LE hro hs (p + 8) (by omega)

private structure SavedFrameMulti (m : Arm64.Mem) (sp0 : UInt64) (orig : Arm64.ArmState) : Prop where
  sx26 : m.readU64LE sp0                 = some orig.regs.x26
  sx25 : m.readU64LE (sp0 + 8)           = some orig.regs.x25
  sx24 : m.readU64LE (sp0 + 0x10)        = some orig.regs.x24
  sx23 : m.readU64LE (sp0 + (0x10 + 8))  = some orig.regs.x23
  sx22 : m.readU64LE (sp0 + 0x20)        = some orig.regs.x22
  sx21 : m.readU64LE (sp0 + (0x20 + 8))  = some orig.regs.x21
  sx20 : m.readU64LE (sp0 + 0x30)        = some orig.regs.x20
  sx19 : m.readU64LE (sp0 + (0x30 + 8))  = some orig.regs.x19
  sx29 : m.readU64LE (sp0 + 0x40)        = some orig.regs.x29
  sx30 : m.readU64LE (sp0 + (0x40 + 8))  = some orig.regs.x30

private theorem SavedFrameMulti.of_memOutsideEq {m m' : Arm64.Mem} {sp0 : UInt64}
    {orig : Arm64.ArmState} {subLo : UInt64} {subLen : Nat}
    (hs : SavedFrameMulti m sp0 orig) (hout : MemOutsideEq m m' subLo subLen)
    (hb : sp0.toNat + 0x50 ≤ UInt64.size)
    (hdisj : subLo.toNat + subLen ≤ sp0.toNat) :
    SavedFrameMulti m' sp0 orig := by
  have : UInt64.size = 2 ^ 64 := rfl
  have rd (off : UInt64) (hoff : decide (off.toNat + 8 ≤ 0x50) = true := by decide) :
      m'.readU64LE (sp0 + off) = m.readU64LE (sp0 + off) := by
    have ho := of_decide_eq_true hoff
    have ht : (sp0 + off).toNat = sp0.toNat + off.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hout.readU64LE (sp0 + off) (by omega) (by omega)
  have rd0 : m'.readU64LE sp0 = m.readU64LE sp0 :=
    hout.readU64LE sp0 (by omega) (by omega)
  exact {
    sx26 := rd0.trans hs.sx26
    sx25 := (rd 8).trans hs.sx25
    sx24 := (rd 0x10).trans hs.sx24
    sx23 := (rd (0x10 + 8)).trans hs.sx23
    sx22 := (rd 0x20).trans hs.sx22
    sx21 := (rd (0x20 + 8)).trans hs.sx21
    sx20 := (rd 0x30).trans hs.sx20
    sx19 := (rd (0x30 + 8)).trans hs.sx19
    sx29 := (rd 0x40).trans hs.sx29
    sx30 := (rd (0x40 + 8)).trans hs.sx30
  }

/-! ### Section 3: Prologue (`idx 0..10`) and shared epilogue + tail `b hwLoop` (`idx 111..118`) -/

private theorem rawExtendHwMulti_prologue {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {uoff ulen : USize} {s_in : UInt32}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hpc : s.pc = Layout.rawExtendHwMultiBase)
    (hrw : s.mem.isRWRange (s.sp - 0x50) 0x50)
    (hw0 : s.getW r0 = s_in)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = uoff.toUInt64)
    (hx3 : s.regs.x3 = ulen.toUInt64) :
    let sp0 := s.sp - 0x50
    ∃ st, Arm64.run code 12 s = some st ∧
      st.pc = (if 768 ≤ ulen then Layout.rawExtendHwMultiBase + 184
               else Layout.rawExtendHwMultiBase + 48) ∧
      st.sp = sp0 ∧
      StackDelta code Layout s.mem st.mem sp0 0x50 ∧
      SavedFrameMulti st.mem sp0 s ∧
      st.getW r1 = s_in ∧
      st.regs.x19 = objPtr ∧
      st.regs.x21 = uoff.toUInt64 ∧
      st.regs.x20 = ulen.toUInt64 ∧
      st.regs.x27 = s.regs.x27 ∧ st.regs.x28 = s.regs.x28 ∧
      st.getD r8  = s.getD r8  ∧ st.getD r9  = s.getD r9  ∧
      st.getD r10 = s.getD r10 ∧ st.getD r11 = s.getD r11 ∧
      st.getD r12 = s.getD r12 ∧ st.getD r13 = s.getD r13 ∧
      st.getD r14 = s.getD r14 ∧ st.getD r15 = s.getD r15 := by
  intro sp0
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only [sp0] at hc hg hpc hrw hw0 hx1 hx2 hx3 ⊢
  dsimp only [getW_mk_r0] at hw0
  subst hpc
  have d0 := StackDelta.refl hrw hc hg
  have w0 := writeU64LE_sp_zero d0.rwRange regs.x26
  have d1 := d0.step64_zero regs.x26
  have w1 := writeU64LE_sp_off d1.rwRange 8 regs.x25
  have d2 := d1.step64 8 regs.x25
  have w2 := writeU64LE_sp_off d2.rwRange 0x10 regs.x24
  have d3 := d2.step64 0x10 regs.x24
  have w3 := writeU64LE_sp_off d3.rwRange (0x10 + 8) regs.x23
  have d4 := d3.step64 (0x10 + 8) regs.x23
  have w4 := writeU64LE_sp_off d4.rwRange 0x20 regs.x22
  have d5 := d4.step64 0x20 regs.x22
  have w5 := writeU64LE_sp_off d5.rwRange (0x20 + 8) regs.x21
  have d6 := d5.step64 (0x20 + 8) regs.x21
  have w6 := writeU64LE_sp_off d6.rwRange 0x30 regs.x20
  have d7 := d6.step64 0x30 regs.x20
  have w7 := writeU64LE_sp_off d7.rwRange (0x30 + 8) regs.x19
  have d8 := d7.step64 (0x30 + 8) regs.x19
  have w8 := writeU64LE_sp_off d8.rwRange 0x40 regs.x29
  have d9 := d8.step64 0x40 regs.x29
  have w9 := writeU64LE_sp_off d9.rwRange (0x40 + 8) regs.x30
  have d10 := d9.step64 (0x40 + 8) regs.x30
  have hb := d10.rwRange.1
  have hhi_iff : ((0x2ff : UInt64) < ulen.toUInt64) ↔ (768 ≤ ulen) := by
    change (767 : Nat) < ulen.toUInt64.toNat ↔ _
    have e768 : (768 : USize).toNat = 768 := by simp
    rw [USize.toNat_toUInt64, USize.le_iff_toNat_le, e768]
    omega
  apply Exists.intro
  apply And.intro
  · mc_step_with step_rawExtendHwMulti hc 0 rawExtendHwMultiInsn [sp_pre_0x50, w0, w1]
    mc_step_with step_rawExtendHwMulti d2.codeLoaded 1 rawExtendHwMultiInsn [w2, w3]
    mc_step_with step_rawExtendHwMulti d4.codeLoaded 2 rawExtendHwMultiInsn [w4, w5]
    mc_step_with step_rawExtendHwMulti d6.codeLoaded 3 rawExtendHwMultiInsn [w6, w7]
    mc_step_with step_rawExtendHwMulti d8.codeLoaded 4 rawExtendHwMultiInsn [w8, w9]
    mc_step step_rawExtendHwMulti d10.codeLoaded 5 rawExtendHwMultiInsn
    mc_step step_rawExtendHwMulti d10.codeLoaded 6 rawExtendHwMultiInsn
    mc_step step_rawExtendHwMulti d10.codeLoaded 7 rawExtendHwMultiInsn
    mc_step step_rawExtendHwMulti d10.codeLoaded 8 rawExtendHwMultiInsn
    mc_step step_rawExtendHwMulti d10.codeLoaded 9 rawExtendHwMultiInsn
    mc_step_with step_rawExtendHwMulti d10.codeLoaded 10 rawExtendHwMultiInsn [hx3]
    mc_step step_rawExtendHwMulti d10.codeLoaded 11 rawExtendHwMultiInsn
    exact Arm64.run_zero _ _
  · refine ⟨?_, rfl, d10, ?_, hw0, hx1, hx2, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only
      by_cases h768 : 768 ≤ ulen
      · have hhi : (0x2ff : UInt64) < ulen.toUInt64 := hhi_iff.mpr h768
        simp only [hhi, h768, ↓reduceIte]
        congr 1
      · have hnhi : ¬ ((0x2ff : UInt64) < ulen.toUInt64) := fun h => h768 (hhi_iff.mp h)
        simp only [hnhi, h768, ↓reduceIte]
        congr 1
    · dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · repeat (first
          | (rw [readU64LE_zero_writeSlot64_u64 hb]; rotate_left; decide)
          | (rw [readU64LE_writeSlot64_zero_same_u64 hb]; decide))
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb
      · solve_slot_read hb

/-- Epilogue (`idx 113..118`): restores `x19..x26, x29, x30` and `sp := orig.sp`, then
tail-jumps to `hwLoop` (`x0 = objPtr`, `x1 = tailI`, `x2 = fin`, `w3 = acc`). -/
private theorem rawExtendHwMulti_epilogue_at113 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s orig : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {tailI fin : USize} (hle : tailI.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size)
    {acc : UInt32}
    (hc : CodeLoaded code s.mem Layout)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.rawExtendHwMultiBase + 452)
    (hsp : s.sp = orig.sp - 0x50)
    (hsaved : SavedFrameMulti s.mem (orig.sp - 0x50) orig)
    (hx0 : s.regs.x0 = objPtr)
    (hx1 : s.regs.x1 = tailI.toUInt64)
    (hx2 : s.regs.x2 = fin.toUInt64)
    (hw3 : s.getW r3 = acc)
    (hx27 : s.regs.x27 = orig.regs.x27) (hx28 : s.regs.x28 = orig.regs.x28)
    (hd8  : s.getD r8  = orig.getD r8)  (hd9  : s.getD r9  = orig.getD r9)
    (hd10 : s.getD r10 = orig.getD r10) (hd11 : s.getD r11 = orig.getD r11)
    (hd12 : s.getD r12 = orig.getD r12) (hd13 : s.getD r13 = orig.getD r13)
    (hd14 : s.getD r14 = orig.getD r14) (hd15 : s.getD r15 = orig.getD r15) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = orig.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend acc (Crc32c.bytes a tailI.toNat fin.toNat) ∧
      s'.mem = s.mem ∧
      CalleeSaved orig s' := by
  have hb118 : BranchAt code (Layout.rawExtendHwMultiBase + 472) Layout.hwLoopBase false := by
    simpa [CodeLayout.symAddr] using
      hc.rawExtendHwMulti.2.1 { idx := 118, isCall := false, target := .fnHwLoop } (by decide)
  have hsp_restore : (orig.sp - 0x50) + 0x50 = orig.sp := u64_sub_add_cancel orig.sp 0x50
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hro hpc hsp hsaved hx0 hx1 hx2 hw3 hx27 hx28
  dsimp only [getW_mk_r3] at hw3
  subst hpc hsp
  mc_step_ex_with step_rawExtendHwMulti hc 113 rawExtendHwMultiInsn [hsaved.sx29, hsaved.sx30]
  mc_step_ex_with step_rawExtendHwMulti hc 114 rawExtendHwMultiInsn [hsaved.sx20, hsaved.sx19]
  mc_step_ex_with step_rawExtendHwMulti hc 115 rawExtendHwMultiInsn [hsaved.sx22, hsaved.sx21]
  mc_step_ex_with step_rawExtendHwMulti hc 116 rawExtendHwMultiInsn [hsaved.sx24, hsaved.sx23]
  mc_step_ex_with step_rawExtendHwMulti hc 117 rawExtendHwMultiInsn [hsaved.sx26, hsaved.sx25, hsp_restore]
  apply run_branch_jump_at hb118
  apply let_cur_state
  intro st
  rcases hwLoop_mc_spec (s := st) (s0 := acc) hs hle hfin hc hro rfl hx0 hx1 hx2 hw3 with
    ⟨kL, s', hrL, hpc', hr0', hmem', hcs'⟩
  exact ⟨kL, s', hrL, hpc', hr0', hmem',
    ⟨hcs'.sp, hcs'.x19, hcs'.x20, hcs'.x21, hcs'.x22, hcs'.x23, hcs'.x24,
     hcs'.x25, hcs'.x26, hcs'.x27.trans hx27, hcs'.x28.trans hx28, hcs'.x29, hcs'.x30,
     hcs'.d8.trans hd8, hcs'.d9.trans hd9, hcs'.d10.trans hd10, hcs'.d11.trans hd11,
     hcs'.d12.trans hd12, hcs'.d13.trans hd13, hcs'.d14.trans hd14, hcs'.d15.trans hd15⟩⟩

/-! ### Section 4: Inlined `hwFold3` loops (`idx 29..45` and `idx 88..108`) -/

/-- Preservation of `SP`, `X19..X29`, and `D8..D15` across internal `bl combine3` calls
(which clobber `X30`, while caller `X30` is saved in `SavedFrameMulti` at `sp0 + 0x48`). -/
private structure KeepNoLR (s s' : Arm64.ArmState) : Prop where
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
  d8  : s'.getD r8 = s.getD r8
  d9  : s'.getD r9 = s.getD r9
  d10 : s'.getD r10 = s.getD r10
  d11 : s'.getD r11 = s.getD r11
  d12 : s'.getD r12 = s.getD r12
  d13 : s'.getD r13 = s.getD r13
  d14 : s'.getD r14 = s.getD r14
  d15 : s'.getD r15 = s.getD r15

private theorem add_lsl1_usize (b res : USize) (hres : res.toNat = 3 * b.toNat) :
    b.toUInt64 + (b.toUInt64 <<< (1 : Nat).toUInt64) = res.toUInt64 := by
  have hus := usize_le_2pow64
  have hres64 : res.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_size res) hus
  apply u64_ext
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, USize.toNat_toUInt64, USize.toNat_toUInt64]
  have h1 : ((1 : Nat).toUInt64).toNat % 64 = 1 := rfl
  rw [h1, Nat.shiftLeft_eq]
  have hb2 : b.toNat * 2 ^ 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hb2, show b.toNat + b.toNat * 2 ^ 1 = res.toNat by omega,
    Nat.mod_eq_of_lt hres64]

/-- Algebraic glue connecting `hwFold3` + tail `rawExtend` to single-slice `rawExtend`. -/
private theorem hwFold3_tail_eq (a : ByteArray) (hs : a.size < USize.size)
    (start stop ws L L2 tailI fin : USize)
    (h1 : 1 ≤ ws.toNat)
    (hwsL : L.toNat = 8 * ws.toNat)
    (hL2 : L2.toNat = 2 * L.toNat)
    (hstop : stop.toNat = start.toNat + L.toNat)
    (htail : tailI.toNat = start.toNat + 3 * L.toNat)
    (hle_f3 : start.toNat ≤ stop.toNat)
    (hal_f3 : (stop.toNat - start.toNat) % 16 = 0)
    (hL_f3 : stop.toNat + 2 * L.toNat ≤ a.size)
    (hle_tail : tailI.toNat ≤ fin.toNat)
    (hfin : fin.toNat ≤ a.size)
    (acc : UInt32) :
    Crc32c.rawExtend
        (Crc32c.hwFold3 a hs start stop ws L L2 hle_f3 hal_f3 hL2 hL_f3 acc 0 0)
        (Crc32c.bytes a tailI.toNat fin.toNat) =
      Crc32c.rawExtend acc (Crc32c.bytes a start.toNat fin.toNat) := by
  rw [Crc32c.hwFold3_spec a hs stop ws L L2 hL2 hL_f3 _ start hle_f3 hal_f3 acc 0 0 rfl]
  have lenA : (Crc32c.bytes a start.toNat stop.toNat).length = 8 * ws.toNat := by
    rw [Crc32c.length_bytes a _ _ (by omega)]; omega
  have lenB : (Crc32c.bytes a (start.toNat + L.toNat) (stop.toNat + L.toNat)).length = 8 * ws.toNat := by
    rw [Crc32c.length_bytes a _ _ (by omega)]; omega
  have lenC : (Crc32c.bytes a (start.toNat + 2 * L.toNat) (stop.toNat + 2 * L.toNat)).length = 8 * ws.toNat := by
    rw [Crc32c.length_bytes a _ _ (by omega)]; omega
  rw [Crc32c.combine3_eq acc ws h1 _ _ _ lenA lenB lenC, ← Crc32c.rawExtend_append]
  have e1 : stop.toNat + L.toNat = start.toNat + 2 * L.toNat := by omega
  have e2 : stop.toNat + 2 * L.toNat = tailI.toNat := by omega
  rw [e1, e2, hstop,
    Crc32c.bytes_append a (i := start.toNat) (m := start.toNat + L.toNat)
      (j := start.toNat + 2 * L.toNat) (by omega) (by omega) (by omega),
    Crc32c.bytes_append a (i := start.toNat) (m := start.toNat + 2 * L.toNat)
      (j := tailI.toNat) (by omega) (by omega) (by omega),
    Crc32c.bytes_append a (i := start.toNat) (m := tailI.toNat)
      (j := fin.toNat) (by omega) hle_tail hfin]

private theorem rawExtendHwMulti_loop1 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {stop ws L L2 : USize}
    (hL8 : 8 ≤ L.toNat)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size) :
    ∀ (rem : Nat) (s : Arm64.ArmState) (i : USize)
      (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 16 = 0)
      (_hrem : stop.toNat - i.toNat = rem) (_hlt : i < stop)
      (s0 s1 s2 : UInt32),
      CodeLoaded code s.mem Layout →
      GlobalsLoaded s.mem Layout →
      s.mem.hasROBytes base a →
      s.pc = Layout.rawExtendHwMultiBase + 116 →
      s.regs.x0 = ws.toUInt64 →
      s.regs.x8 = L.toUInt64 →
      s.regs.x10 = L2.toUInt64 →
      s.regs.x9 = stop.toUInt64 →
      s.regs.x11 = base + i.toUInt64 →
      s.regs.x12 = (i + 8).toUInt64 →
      s.getW r1 = s0 → s.getW r2 = s1 → s.getW r3 = s2 →
      ∃ k s', Arm64.run code k s = some s' ∧
        s'.pc = Layout.rawExtendHwMultiBase + 276 ∧
        s'.getW r0 = Crc32c.hwFold3 a hs i stop ws L L2 hi hal hL2 hL s0 s1 s2 ∧
        s'.mem = s.mem ∧
        KeepNoLR s s' := by
  have hus := usize_le_2pow64
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s i hi hal hrem hlt s0 s1 s2 hc hg hro hpc hx0 hx8 hx10 hx9 hx11 hx12 hw1 hw2 hw3
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have h16le : i.toNat + 16 ≤ stop.toNat := by
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    have h16 : (i + 16).toNat = i.toNat + 16 := usize_add16_toNat i (by omega)
    have hi8 : (i + 8).toNat = i.toNat + 8 := usize_add8_toNat i (by omega)
    have hnext8 : ((i + 16) + 8).toNat = (i + 8).toNat + 16 := by
      rw [usize_add8_toNat (i + 16) (by omega), h16, hi8]
    have hi1 : (i + L).toNat = i.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
      rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
    have hle' : (i + 16).toNat ≤ stop.toNat := by omega
    have hal' : (stop.toNat - (i + 16).toNat) % 16 = 0 := by omega
    have hb0 : i.toNat + 16 ≤ a.size := by omega
    have hb1 : (i + L).toNat + 16 ≤ a.size := by omega
    have hb2 : (i + L2).toNat + 16 ≤ a.size := by omega
    have b0 := block128Reads_of_ro hro hs i hb0
    have b1 := block128Reads_of_ro hro hs (i + L) hb1
    have b2 := block128Reads_of_ro hro hs (i + L2) hb2
    have uL1 : i.toUInt64 + L.toUInt64 = (i + L).toUInt64 := usize_add_u64 hi1
    have uL2 : i.toUInt64 + L2.toUInt64 = (i + L2).toUInt64 :=
      usize_add_u64 (by rw [hi2, hL2])
    have u_x13 : (i + 8).toUInt64 + 8 = (i + 16).toUInt64 :=
      usize_add_lit_u64 (by rw [h16, hi8]; rfl)
    have u_x12 : (i + 8).toUInt64 + 0x10 = ((i + 16) + 8).toUInt64 :=
      usize_add_lit_u64 hnext8
    have u_x11 : i.toUInt64 + 0x10 = (i + 16).toUInt64 :=
      usize_add_lit_u64 h16
    have hlt_iff : ((i + 16).toUInt64 < stop.toUInt64) ↔ (i + 16 < stop) := by
      change (i + 16).toUInt64.toNat < stop.toUInt64.toNat ↔ _
      rw [USize.toNat_toUInt64, USize.toNat_toUInt64, USize.lt_iff_toNat_lt]
    rw [Crc32c.hwFold3]
    simp only [hlt, ↓reduceDIte]
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hc hg hro hpc hx0 hx8 hx10 hx9 hx11 hx12 hw1 hw2 hw3
    dsimp only [getW_mk_r1, getW_mk_r2, getW_mk_r3] at hw1 hw2 hw3
    subst hpc
    mc_step_ex_with step_rawExtendHwMulti hc 29 rawExtendHwMultiInsn [hx11, b0.r0, b0.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 30 rawExtendHwMultiInsn [hw1]
    mc_step_ex step_rawExtendHwMulti hc 31 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 32 rawExtendHwMultiInsn [hx11, hx8, uL1]
    mc_step_ex_with step_rawExtendHwMulti hc 33 rawExtendHwMultiInsn [b1.r0, b1.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 34 rawExtendHwMultiInsn [hw2]
    mc_step_ex step_rawExtendHwMulti hc 35 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 36 rawExtendHwMultiInsn [hx11, hx10, uL2]
    mc_step_ex_with step_rawExtendHwMulti hc 37 rawExtendHwMultiInsn [b2.r0, b2.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 38 rawExtendHwMultiInsn [hw3]
    mc_step_ex step_rawExtendHwMulti hc 39 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 40 rawExtendHwMultiInsn [hx12, u_x13]
    mc_step_ex_with step_rawExtendHwMulti hc 41 rawExtendHwMultiInsn [hx12, u_x12]
    mc_step_ex_with step_rawExtendHwMulti hc 42 rawExtendHwMultiInsn [hx11, u_x11]
    mc_step_ex_with step_rawExtendHwMulti hc 43 rawExtendHwMultiInsn [hx9]
    by_cases hmore : i + 16 < stop
    · have hmore_u : (i + 16).toUInt64 < stop.toUInt64 := hlt_iff.mpr hmore
      mc_step_ex_with step_rawExtendHwMulti hc 44 rawExtendHwMultiInsn [hmore_u]
      apply let_cur_state
      intro st1
      rcases ih (stop.toNat - (i + 16).toNat) (by omega) st1 (i + 16)
          hle' hal' rfl hmore
          (Crc32c.crc128 a hs i hb0 s0)
          (Crc32c.crc128 a hs (i + L) hb1 s1)
          (Crc32c.crc128 a hs (i + L2) hb2 s2)
          hc hg hro (by dsimp only [st1]; congr 1) hx0 rfl rfl rfl rfl rfl
          (by dsimp only [st1, getW_mk_r1]; exact toUInt32_toUInt64 _)
          (by dsimp only [st1, getW_mk_r2]; exact toUInt32_toUInt64 _)
          (by dsimp only [st1, getW_mk_r3]; exact toUInt32_toUInt64 _) with
        ⟨k2, s', hr2, hpc2, hr0_2, hmem2, hkl2⟩
      exact ⟨k2, s', hr2, hpc2, hr0_2, hmem2,
        ⟨hkl2.sp, hkl2.x19, hkl2.x20, hkl2.x21, hkl2.x22, hkl2.x23, hkl2.x24,
         hkl2.x25, hkl2.x26, hkl2.x27, hkl2.x28, hkl2.x29,
         hkl2.d8, hkl2.d9, hkl2.d10, hkl2.d11, hkl2.d12, hkl2.d13, hkl2.d14, hkl2.d15⟩⟩
    · have hnmore_u : ¬ ((i + 16).toUInt64 < stop.toUInt64) := fun h => hmore (hlt_iff.mp h)
      have hb68 : BranchAt code (Layout.rawExtendHwMultiBase + 272) Layout.combine3Base true := by
        simpa [CodeLayout.symAddr] using
          hc.rawExtendHwMulti.2.1 { idx := 68, isCall := true, target := .fnCombine3 } (by decide)
      mc_step_ex_with step_rawExtendHwMulti hc 44 rawExtendHwMultiInsn [hnmore_u]
      mc_step_ex step_rawExtendHwMulti hc 45 rawExtendHwMultiInsn
      apply run_branch_call_at hb68
      dsimp only [setX_mk_r30]
      apply let_cur_state
      intro stC
      rw [Crc32c.hwFold3]
      simp only [hmore, ↓reduceDIte]
      rcases combine3_mc_spec (s := stC) (ws := ws)
          (s0 := Crc32c.crc128 a hs i hb0 s0)
          (s1 := Crc32c.crc128 a hs (i + L) hb1 s1)
          (s2 := Crc32c.crc128 a hs (i + L2) hb2 s2)
          hc hg rfl hx0
          (by dsimp only [stC, getW_mk_r1]; exact toUInt32_toUInt64 _)
          (by dsimp only [stC, getW_mk_r2]; exact toUInt32_toUInt64 _)
          (by dsimp only [stC, getW_mk_r3]; exact toUInt32_toUInt64 _) with
        ⟨kC, s', hrC, hpcC, hr0C, hmemC, hcsC⟩
      refine ⟨kC, s', hrC, ?_, hr0C, hmemC,
        ⟨hcsC.sp, hcsC.x19, hcsC.x20, hcsC.x21, hcsC.x22, hcsC.x23, hcsC.x24,
         hcsC.x25, hcsC.x26, hcsC.x27, hcsC.x28, hcsC.x29,
         hcsC.d8, hcsC.d9, hcsC.d10, hcsC.d11, hcsC.d12, hcsC.d13, hcsC.d14, hcsC.d15⟩⟩
      exact hpcC.trans (by dsimp only [stC]; simp only [UInt64.add_assoc]; rfl)

private theorem rawExtendHwMulti_loop2 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {base : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {stop ws L L2 : USize}
    (hL8 : 8 ≤ L.toNat)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size) :
    ∀ (rem : Nat) (s : Arm64.ArmState) (i : USize)
      (hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 16 = 0)
      (_hrem : stop.toNat - i.toNat = rem) (_hlt : i < stop)
      (s0 s1 s2 : UInt32),
      CodeLoaded code s.mem Layout →
      GlobalsLoaded s.mem Layout →
      s.mem.hasROBytes base a →
      s.pc = Layout.rawExtendHwMultiBase + 352 →
      s.regs.x0 = ws.toUInt64 →
      s.regs.x9 = L.toUInt64 →
      s.regs.x11 = L2.toUInt64 →
      s.regs.x10 = stop.toUInt64 →
      s.regs.x12 = base + i.toUInt64 →
      s.regs.x13 = (i + 8).toUInt64 →
      s.getW r8 = s0 → s.getW r2 = s1 → s.getW r3 = s2 →
      ∃ k s', Arm64.run code k s = some s' ∧
        s'.pc = Layout.rawExtendHwMultiBase + 436 ∧
        s'.getW r0 = Crc32c.hwFold3 a hs i stop ws L L2 hi hal hL2 hL s0 s1 s2 ∧
        s'.mem = s.mem ∧
        KeepNoLR s s' := by
  have hus := usize_le_2pow64
  intro rem
  induction rem using Nat.strong_induction_on with
  | _ rem ih =>
    intro s i hi hal hrem hlt s0 s1 s2 hc hg hro hpc hx0 hx9 hx11 hx10 hx12 hx13 hw8 hw2 hw3
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have h16le : i.toNat + 16 ≤ stop.toNat := by
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    have h16 : (i + 16).toNat = i.toNat + 16 := usize_add16_toNat i (by omega)
    have hi8 : (i + 8).toNat = i.toNat + 8 := usize_add8_toNat i (by omega)
    have hnext8 : ((i + 16) + 8).toNat = (i + 8).toNat + 16 := by
      rw [usize_add8_toNat (i + 16) (by omega), h16, hi8]
    have hi1 : (i + L).toNat = i.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
      rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
    have hle' : (i + 16).toNat ≤ stop.toNat := by omega
    have hal' : (stop.toNat - (i + 16).toNat) % 16 = 0 := by omega
    have hb0 : i.toNat + 16 ≤ a.size := by omega
    have hb1 : (i + L).toNat + 16 ≤ a.size := by omega
    have hb2 : (i + L2).toNat + 16 ≤ a.size := by omega
    have b0 := block128Reads_of_ro hro hs i hb0
    have b1 := block128Reads_of_ro hro hs (i + L) hb1
    have b2 := block128Reads_of_ro hro hs (i + L2) hb2
    have uL1 : i.toUInt64 + L.toUInt64 = (i + L).toUInt64 := usize_add_u64 hi1
    have uL2 : i.toUInt64 + L2.toUInt64 = (i + L2).toUInt64 :=
      usize_add_u64 (by rw [hi2, hL2])
    have u_x14 : (i + 8).toUInt64 + 8 = (i + 16).toUInt64 :=
      usize_add_lit_u64 (by rw [h16, hi8]; rfl)
    have u_x13 : (i + 8).toUInt64 + 0x10 = ((i + 16) + 8).toUInt64 :=
      usize_add_lit_u64 hnext8
    have u_x12 : i.toUInt64 + 0x10 = (i + 16).toUInt64 :=
      usize_add_lit_u64 h16
    have hlt_iff : ((i + 16).toUInt64 < stop.toUInt64) ↔ (i + 16 < stop) := by
      change (i + 16).toUInt64.toNat < stop.toUInt64.toNat ↔ _
      rw [USize.toNat_toUInt64, USize.toNat_toUInt64, USize.lt_iff_toNat_lt]
    rw [Crc32c.hwFold3]
    simp only [hlt, ↓reduceDIte]
    rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
    dsimp only at hc hg hro hpc hx0 hx9 hx11 hx10 hx12 hx13 hw8 hw2 hw3
    dsimp only [getW_mk_r8, getW_mk_r2, getW_mk_r3] at hw8 hw2 hw3
    subst hpc
    mc_step_ex_with step_rawExtendHwMulti hc 88 rawExtendHwMultiInsn [hx12, b0.r0, b0.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 89 rawExtendHwMultiInsn [hw8]
    mc_step_ex step_rawExtendHwMulti hc 90 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 91 rawExtendHwMultiInsn [hx12, hx9, uL1]
    mc_step_ex_with step_rawExtendHwMulti hc 92 rawExtendHwMultiInsn [b1.r0, b1.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 93 rawExtendHwMultiInsn [hw2]
    mc_step_ex step_rawExtendHwMulti hc 94 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 95 rawExtendHwMultiInsn [hx12, hx11, uL2]
    mc_step_ex_with step_rawExtendHwMulti hc 96 rawExtendHwMultiInsn [b2.r0, b2.r1]
    mc_step_ex_with step_rawExtendHwMulti hc 97 rawExtendHwMultiInsn [hw3]
    mc_step_ex step_rawExtendHwMulti hc 98 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc 99 rawExtendHwMultiInsn [hx13, u_x14]
    mc_step_ex_with step_rawExtendHwMulti hc 100 rawExtendHwMultiInsn [hx13, u_x13]
    mc_step_ex_with step_rawExtendHwMulti hc 101 rawExtendHwMultiInsn [hx12, u_x12]
    mc_step_ex_with step_rawExtendHwMulti hc 102 rawExtendHwMultiInsn [hx10]
    by_cases hmore : i + 16 < stop
    · have hmore_u : (i + 16).toUInt64 < stop.toUInt64 := hlt_iff.mpr hmore
      mc_step_ex_with step_rawExtendHwMulti hc 103 rawExtendHwMultiInsn [hmore_u]
      apply let_cur_state
      intro st1
      rcases ih (stop.toNat - (i + 16).toNat) (by omega) st1 (i + 16)
          hle' hal' rfl hmore
          (Crc32c.crc128 a hs i hb0 s0)
          (Crc32c.crc128 a hs (i + L) hb1 s1)
          (Crc32c.crc128 a hs (i + L2) hb2 s2)
          hc hg hro (by dsimp only [st1]; congr 1) hx0 rfl rfl rfl rfl rfl
          (by dsimp only [st1, getW_mk_r8]; exact toUInt32_toUInt64 _)
          (by dsimp only [st1, getW_mk_r2]; exact toUInt32_toUInt64 _)
          (by dsimp only [st1, getW_mk_r3]; exact toUInt32_toUInt64 _) with
        ⟨k2, s', hr2, hpc2, hr0_2, hmem2, hkl2⟩
      exact ⟨k2, s', hr2, hpc2, hr0_2, hmem2,
        ⟨hkl2.sp, hkl2.x19, hkl2.x20, hkl2.x21, hkl2.x22, hkl2.x23, hkl2.x24,
         hkl2.x25, hkl2.x26, hkl2.x27, hkl2.x28, hkl2.x29,
         hkl2.d8, hkl2.d9, hkl2.d10, hkl2.d11, hkl2.d12, hkl2.d13, hkl2.d14, hkl2.d15⟩⟩
    · have hnmore_u : ¬ ((i + 16).toUInt64 < stop.toUInt64) := fun h => hmore (hlt_iff.mp h)
      have hb108 : BranchAt code (Layout.rawExtendHwMultiBase + 432) Layout.combine3Base true := by
        simpa [CodeLayout.symAddr] using
          hc.rawExtendHwMulti.2.1 { idx := 108, isCall := true, target := .fnCombine3 } (by decide)
      mc_step_ex_with step_rawExtendHwMulti hc 103 rawExtendHwMultiInsn [hnmore_u]
      mc_step_ex step_rawExtendHwMulti hc 104 rawExtendHwMultiInsn
      mc_step_ex step_rawExtendHwMulti hc 107 rawExtendHwMultiInsn
      apply run_branch_call_at hb108
      dsimp only [setX_mk_r30]
      apply let_cur_state
      intro stC
      rw [Crc32c.hwFold3]
      simp only [hmore, ↓reduceDIte]
      rcases combine3_mc_spec (s := stC) (ws := ws)
          (s0 := Crc32c.crc128 a hs i hb0 s0)
          (s1 := Crc32c.crc128 a hs (i + L) hb1 s1)
          (s2 := Crc32c.crc128 a hs (i + L2) hb2 s2)
          hc hg rfl hx0
          (by dsimp only [stC, getW_mk_r1]; exact toUInt32_toUInt64 _)
          (by dsimp only [stC, getW_mk_r2]; exact toUInt32_toUInt64 _)
          (by dsimp only [stC, getW_mk_r3]; exact toUInt32_toUInt64 _) with
        ⟨kC, s', hrC, hpcC, hr0C, hmemC, hcsC⟩
      refine ⟨kC, s', hrC, ?_, hr0C, hmemC,
        ⟨hcsC.sp, hcsC.x19, hcsC.x20, hcsC.x21, hcsC.x22, hcsC.x23, hcsC.x24,
         hcsC.x25, hcsC.x26, hcsC.x27, hcsC.x28, hcsC.x29,
         hcsC.d8, hcsC.d9, hcsC.d10, hcsC.d11, hcsC.d12, hcsC.d13, hcsC.d14, hcsC.d15⟩⟩
      exact hpcC.trans (by dsimp only [stC]; simp only [UInt64.add_assoc]; rfl)

/-! ### Section 5: Path 1 (`96 ≤ ulen < 768`, `idx 12..71, 111..118`) and Path 2 (`768 ≤ ulen`, `idx 46..118`) -/

private theorem rawExtendHwMulti_path1 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s orig : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {uoff ulen : USize} (hsz : uoff.toNat + ulen.toNat ≤ a.size)
    (h96 : 96 ≤ ulen.toNat) (hlt768 : ulen.toNat < 768)
    {s_in : UInt32}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.rawExtendHwMultiBase + 48)
    (hsp : s.sp = orig.sp - 0x50)
    (hsaved : SavedFrameMulti s.mem (orig.sp - 0x50) orig)
    (hw1 : s.getW r1 = s_in)
    (hx19 : s.regs.x19 = objPtr)
    (hx21 : s.regs.x21 = uoff.toUInt64)
    (hx20 : s.regs.x20 = ulen.toUInt64)
    (hx27 : s.regs.x27 = orig.regs.x27) (hx28 : s.regs.x28 = orig.regs.x28)
    (hd8  : s.getD r8  = orig.getD r8)  (hd9  : s.getD r9  = orig.getD r9)
    (hd10 : s.getD r10 = orig.getD r10) (hd11 : s.getD r11 = orig.getD r11)
    (hd12 : s.getD r12 = orig.getD r12) (hd13 : s.getD r13 = orig.getD r13)
    (hd14 : s.getD r14 = orig.getD r14) (hd15 : s.getD r15 = orig.getD r15) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = orig.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + ulen.toNat)) ∧
      s'.mem = s.mem ∧
      CalleeSaved orig s' := by
  have hus := usize_le_2pow64
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e48 : (48 : USize).toNat = 48 := by simp
  have e16 : (16 : USize).toNat = 16 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  obtain ⟨blocks, d_blocks⟩ : ∃ v, v = ulen / 48 := ⟨_, rfl⟩
  obtain ⟨ws, d_ws⟩ : ∃ v, v = blocks * 2 := ⟨_, rfl⟩
  obtain ⟨L, d_L⟩ : ∃ v, v = blocks * 16 := ⟨_, rfl⟩
  obtain ⟨L2, d_L2⟩ : ∃ v, v = 2 * L := ⟨_, rfl⟩
  obtain ⟨b3, d_b3⟩ : ∃ v, v = ws + blocks := ⟨_, rfl⟩
  obtain ⟨L3, d_L3⟩ : ∃ v, v = 3 * L := ⟨_, rfl⟩
  obtain ⟨stop, d_stop⟩ : ∃ v, v = uoff + L := ⟨_, rfl⟩
  obtain ⟨tailI, d_tail⟩ : ∃ v, v = uoff + L3 := ⟨_, rfl⟩
  obtain ⟨fin, d_fin⟩ : ∃ v, v = uoff + ulen := ⟨_, rfl⟩
  have hblocks : blocks.toNat = ulen.toNat / 48 := by
    rw [d_blocks, USize.toNat_div, e48]
  have hws : ws.toNat = blocks.toNat * 2 := by
    rw [d_ws, USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL : L.toNat = blocks.toNat * 16 := by
    rw [d_L, USize.toNat_mul, e16]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : L2.toNat = 2 * L.toNat := by
    rw [d_L2, USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hb3 : b3.toNat = ws.toNat + blocks.toNat := by
    rw [d_b3, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : L3.toNat = 3 * L.toNat := by
    rw [d_L3, USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hstop : stop.toNat = uoff.toNat + L.toNat := by
    rw [d_stop, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have htail : tailI.toNat = uoff.toNat + L3.toNat := by
    rw [d_tail, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hfin : fin.toNat = uoff.toNat + ulen.toNat := by
    rw [d_fin, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have huoff8 : (uoff + 8).toNat = uoff.toNat + 8 := usize_add8_toNat uoff (by omega)
  have hdiv48 :
      ((ulen.toUInt64.toUInt32 * 0xaaab) >>> (21 : Nat).toUInt32).toUInt64 = blocks.toUInt64 := by
    rw [d_blocks]; exact div48_u32_magic ulen hlt768
  have u_ws : blocks.toUInt64.toUInt32.toUInt64 <<< (1 : Nat).toUInt64 = ws.toUInt64 :=
    ubfiz_shl blocks ws 1 (by decide) (by omega) (by omega)
  have u_L : blocks.toUInt64.toUInt32.toUInt64 <<< (4 : Nat).toUInt64 = L.toUInt64 :=
    ubfiz_shl blocks L 4 (by decide) (by omega) (by omega)
  have u_L2 : blocks.toUInt64.toUInt32.toUInt64 <<< (5 : Nat).toUInt64 = L2.toUInt64 :=
    ubfiz_shl blocks L2 5 (by decide) (by omega) (by omega)
  have u_b3 : ws.toUInt64 + blocks.toUInt64 = b3.toUInt64 := usize_add_u64 hb3
  have u_L3 : b3.toUInt64 <<< (4 : Nat).toUInt64 = L3.toUInt64 :=
    lsl64_usize b3 L3 4 (by decide) (by omega)
  have u_stop : L.toUInt64 + uoff.toUInt64 = stop.toUInt64 :=
    usize_add_u64 (by omega)
  have u_uoff8 : uoff.toUInt64 + 8 = (uoff + 8).toUInt64 := usize_add_lit_u64 huoff8
  have u_tail : L3.toUInt64 + uoff.toUInt64 = tailI.toUInt64 := usize_add_u64 (by omega)
  have u_fin : ulen.toUInt64 + uoff.toUInt64 = fin.toUInt64 := usize_add_u64 (by omega)
  have hnls : ¬ (stop.toUInt64 ≤ uoff.toUInt64) := by
    intro hle64
    have : stop.toUInt64.toNat ≤ uoff.toUInt64.toNat := hle64
    rw [USize.toNat_toUInt64, USize.toNat_toUInt64] at this
    omega
  have hlt_stop : uoff < stop := USize.lt_iff_toNat_lt.mpr (by omega)
  have hle_f3 : uoff.toNat ≤ stop.toNat := by omega
  have hal_f3 : (stop.toNat - uoff.toNat) % 16 = 0 := by omega
  have hL_f3 : stop.toNat + 2 * L.toNat ≤ a.size := by omega
  obtain ⟨base, hbase⟩ : ∃ base : UInt64, objPtr + 0x18 = base := ⟨objPtr + 0x18, rfl⟩
  rw [hbase] at hro
  have hbase_uoff : objPtr + (uoff.toUInt64 + 0x18) = base + uoff.toUInt64 := by
    rw [← hbase, UInt64.add_comm uoff.toUInt64 0x18, ← UInt64.add_assoc]
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at hc hg hro hpc hsp hsaved hw1 hx19 hx21 hx20 hx27 hx28
  dsimp only [getW_mk_r1] at hw1
  subst hpc
  mc_step_ex_with step_rawExtendHwMulti hc 12 rawExtendHwMultiInsn [hx20, and_ffff_lt768 ulen hlt768]
  mc_step_ex_with step_rawExtendHwMulti hc 13 rawExtendHwMultiInsn [movz32_aaab]
  mc_step_ex_with step_rawExtendHwMulti hc 14 rawExtendHwMultiInsn [UInt32.zero_add]
  mc_step_ex_with step_rawExtendHwMulti hc 15 rawExtendHwMultiInsn [hdiv48]
  mc_step_ex_with step_rawExtendHwMulti hc 16 rawExtendHwMultiInsn [u_ws]
  mc_step_ex_with step_rawExtendHwMulti hc 17 rawExtendHwMultiInsn [u_L]
  mc_step_ex_with step_rawExtendHwMulti hc 18 rawExtendHwMultiInsn [u_b3]
  mc_step_ex_with step_rawExtendHwMulti hc 19 rawExtendHwMultiInsn [u_L3]
  mc_step_ex_with step_rawExtendHwMulti hc 20 rawExtendHwMultiInsn [hx21, u_stop]
  mc_step_ex_with step_rawExtendHwMulti hc 21 rawExtendHwMultiInsn [hx21]
  mc_step_ex_with step_rawExtendHwMulti hc 22 rawExtendHwMultiInsn [hnls]
  mc_step_ex step_rawExtendHwMulti hc 23 rawExtendHwMultiInsn
  mc_step_ex step_rawExtendHwMulti hc 24 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc 25 rawExtendHwMultiInsn [u_L2]
  mc_step_ex_with step_rawExtendHwMulti hc 26 rawExtendHwMultiInsn [hx19, hx21]
  mc_step_ex_with step_rawExtendHwMulti hc 27 rawExtendHwMultiInsn [hx21, u_uoff8]
  mc_step_ex_with step_rawExtendHwMulti hc 28 rawExtendHwMultiInsn [hbase_uoff]
  apply let_cur_state
  intro st0
  rcases rawExtendHwMulti_loop1 hs (by omega) hL2 hL_f3 (stop.toNat - uoff.toNat) st0 uoff
      hle_f3 hal_f3 rfl hlt_stop s_in 0 0
      hc hg hro (by dsimp only [st0]; congr 1) rfl rfl rfl rfl rfl rfl
      (by dsimp only [st0, getW_mk_r1]; exact hw1)
      (by dsimp only [st0, getW_mk_r2]; rfl)
      (by dsimp only [st0, getW_mk_r3]; rfl) with
    ⟨kL, stL, hrL, hpcL, hr0L, hmemL, hkl⟩
  apply run_bind_exists hrL
  let s3 := Crc32c.hwFold3 a hs uoff stop ws L L2 hle_f3 hal_f3 hL2 hL_f3 s_in 0 0
  have hspL  : stL.sp = orig.sp - 0x50 := hkl.sp.trans hsp
  have hx19L : stL.regs.x19 = objPtr := hkl.x19
  have hx20L : stL.regs.x20 = ulen.toUInt64 := hkl.x20
  have hx21L : stL.regs.x21 = uoff.toUInt64 := hkl.x21
  have hx22L : stL.regs.x22 = L3.toUInt64 := hkl.x22
  have hx27L : stL.regs.x27 = orig.regs.x27 := hkl.x27.trans hx27
  have hx28L : stL.regs.x28 = orig.regs.x28 := hkl.x28.trans hx28
  have hd8L  : stL.getD r8  = orig.getD r8  := hkl.d8.trans hd8
  have hd9L  : stL.getD r9  = orig.getD r9  := hkl.d9.trans hd9
  have hd10L : stL.getD r10 = orig.getD r10 := hkl.d10.trans hd10
  have hd11L : stL.getD r11 = orig.getD r11 := hkl.d11.trans hd11
  have hd12L : stL.getD r12 = orig.getD r12 := hkl.d12.trans hd12
  have hd13L : stL.getD r13 = orig.getD r13 := hkl.d13.trans hd13
  have hd14L : stL.getD r14 = orig.getD r14 := hkl.d14.trans hd14
  have hd15L : stL.getD r15 = orig.getD r15 := hkl.d15.trans hd15
  rcases stL with ⟨regsL, spL, simdL, nzcvL, pcL, memL⟩
  dsimp only at hpcL hmemL hspL hx19L hx20L hx21L hx22L hx27L hx28L
  dsimp only [getW_mk_r0] at hr0L
  subst hpcL hmemL
  mc_step_ex step_rawExtendHwMulti hc 69 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc 70 rawExtendHwMultiInsn [hx22L, hx21L, u_tail]
  mc_step_ex step_rawExtendHwMulti hc 71 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc 111 rawExtendHwMultiInsn [hx20L, hx21L, u_fin]
  mc_step_ex_with step_rawExtendHwMulti hc 112 rawExtendHwMultiInsn [hx19L]
  apply let_cur_state
  intro stE
  have hro_orig : Arm64.Mem.hasROBytes memL (objPtr + 0x18) a := by rw [hbase]; exact hro
  rcases rawExtendHwMulti_epilogue_at113 (s := stE) (orig := orig) hs
      (tailI := tailI) (fin := fin) (by omega) (by omega) (acc := s3)
      hc hro_orig (by dsimp only [stE]; congr 1) hspL hsaved rfl rfl rfl
      (by dsimp only [stE, getW_mk_r3]; exact hr0L)
      hx27L hx28L hd8L hd9L hd10L hd11L hd12L hd13L hd14L hd15L with
    ⟨kE, s', hrE, hpcE, hr0E, hmemE, hcsE⟩
  refine ⟨kE, s', hrE, hpcE, ?_, hmemE, hcsE⟩
  rw [hr0E]
  dsimp only [s3]
  rw [hwFold3_tail_eq a hs uoff stop ws L L2 tailI fin
    (by omega) (by omega) hL2 hstop (by omega) hle_f3 hal_f3 hL_f3 (by omega) (by omega) s_in,
    hfin]

private theorem rawExtendHwMulti_path2 {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s orig : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {uoff ulen : USize} (hsz : uoff.toNat + ulen.toNat ≤ a.size)
    (h768 : 768 ≤ ulen.toNat)
    {s_in : UInt32}
    (hsp_orig_lo : 0x150 ≤ orig.sp.toNat)
    (d_full1 : StackDelta code Layout orig.mem s.mem (orig.sp - 0x150) 0x150)
    (hb_sp0 : (orig.sp - 0x50).toNat + 0x50 ≤ UInt64.size)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.rawExtendHwMultiBase + 184)
    (hsp : s.sp = orig.sp - 0x50)
    (hsaved : SavedFrameMulti s.mem (orig.sp - 0x50) orig)
    (hw1 : s.getW r1 = s_in)
    (hx19 : s.regs.x19 = objPtr)
    (hx21 : s.regs.x21 = uoff.toUInt64)
    (hx20 : s.regs.x20 = ulen.toUInt64)
    (hx27 : s.regs.x27 = orig.regs.x27) (hx28 : s.regs.x28 = orig.regs.x28)
    (hd8  : s.getD r8  = orig.getD r8)  (hd9  : s.getD r9  = orig.getD r9)
    (hd10 : s.getD r10 = orig.getD r10) (hd11 : s.getD r11 = orig.getD r11)
    (hd12 : s.getD r12 = orig.getD r12) (hd13 : s.getD r13 = orig.getD r13)
    (hd14 : s.getD r14 = orig.getD r14) (hd15 : s.getD r15 = orig.getD r15) :
    ∃ k s', Arm64.run code k s = some s' ∧
      s'.pc = orig.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + ulen.toNat)) ∧
      StackDelta code Layout orig.mem s'.mem (orig.sp - 0x150) 0x150 ∧
      CalleeSaved orig s' := by
  have hus := usize_le_2pow64
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have : UInt64.size = 2 ^ 64 := rfl
  have e384 : (384 : USize).toNat = 384 := by simp
  have e48 : (48 : USize).toNat = 48 := by simp
  have e16 : (16 : USize).toNat = 16 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  obtain ⟨blocks6, d_blocks6⟩ : ∃ v, v = ulen / 384 := ⟨_, rfl⟩
  obtain ⟨b6_3, d_b6_3⟩ : ∃ v, v = 3 * blocks6 := ⟨_, rfl⟩
  obtain ⟨consumed, d_cons⟩ : ∃ v, v = blocks6 * 384 := ⟨_, rfl⟩
  obtain ⟨rem, d_rem⟩ : ∃ v, v = ulen - consumed := ⟨_, rfl⟩
  obtain ⟨mid, d_mid⟩ : ∃ v, v = uoff + consumed := ⟨_, rfl⟩
  obtain ⟨fin, d_fin⟩ : ∃ v, v = uoff + ulen := ⟨_, rfl⟩
  have hblocks6 : blocks6.toNat = ulen.toNat / 384 := by
    rw [d_blocks6, USize.toNat_div, e384]
  have hb1 : 1 ≤ blocks6.toNat := by omega
  have hb6_3 : b6_3.toNat = 3 * blocks6.toNat := by
    rw [d_b6_3, USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hcons : consumed.toNat = blocks6.toNat * 384 := by
    rw [d_cons, USize.toNat_mul, e384]; exact Nat.mod_eq_of_lt (by omega)
  have hrem : rem.toNat = ulen.toNat - consumed.toNat := by
    rw [d_rem]
    exact USize.toNat_sub_of_le ulen consumed (USize.le_iff_toNat_le.mpr (by omega))
  have hrem_lt384 : rem.toNat < 384 := by omega
  have hmid : mid.toNat = uoff.toNat + consumed.toNat := by
    rw [d_mid, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hfin : fin.toNat = uoff.toNat + ulen.toNat := by
    rw [d_fin, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hsz6 : uoff.toNat + blocks6.toNat * 384 ≤ a.size := by omega
  obtain ⟨um8, dum8⟩ : ∃ v : UInt64,
      UInt64.ofNat ((ulen.toUInt64.toNat * (0xaaaaaaaaaaaaaaab : UInt64).toNat) >>> 64) = v :=
    ⟨_, rfl⟩
  have hdiv384 : um8 >>> (8 : Nat).toUInt64 = blocks6.toUInt64 := by
    rw [← dum8, d_blocks6]; exact umulh_div384 ulen
  have u_b6_3 : blocks6.toUInt64 + (blocks6.toUInt64 <<< (1 : Nat).toUInt64) = b6_3.toUInt64 :=
    add_lsl1_usize blocks6 b6_3 hb6_3
  have u_cons : b6_3.toUInt64 <<< (7 : Nat).toUInt64 = consumed.toUInt64 :=
    lsl64_usize b6_3 consumed 7 (by decide) (by omega)
  have u_rem : ulen.toUInt64 - consumed.toUInt64 = rem.toUInt64 :=
    usize_sub_u64 (by omega) hrem
  have u_mid : consumed.toUInt64 + uoff.toUInt64 = mid.toUInt64 := usize_add_u64 (by omega)
  have u_mid' : uoff.toUInt64 + consumed.toUInt64 = mid.toUInt64 := usize_add_u64 hmid
  have u_fin : ulen.toUInt64 + uoff.toUInt64 = fin.toUInt64 := usize_add_u64 (by omega)
  have hsp_150 : (orig.sp - 0x150).toNat = orig.sp.toNat - 0x150 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x150 ≤ orig.sp.toNat; omega)
  have hsp_50 : (orig.sp - 0x50).toNat = orig.sp.toNat - 0x50 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x50 ≤ orig.sp.toNat; omega)
  have hc1 := d_full1.codeLoaded
  have hg1 := d_full1.globalsLoaded
  have hb56 : BranchAt code (Layout.rawExtendHwMultiBase + 224) Layout.hwFold6Base true := by
    simpa [CodeLayout.symAddr] using
      hc1.rawExtendHwMulti.2.1 { idx := 56, isCall := true, target := .fnHwFold6 } (by decide)
  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩
  dsimp only at d_full1 hc1 hg1 hro hpc hsp hsaved hw1 hx19 hx21 hx20 hx27 hx28
  dsimp only [getW_mk_r1] at hw1
  subst hpc hsp
  mc_step_ex step_rawExtendHwMulti hc1 46 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc1 47 rawExtendHwMultiInsn [movk_magic_aaab]
  mc_step_ex_with step_rawExtendHwMulti hc1 48 rawExtendHwMultiInsn [hx20, dum8]
  mc_step_ex_with step_rawExtendHwMulti hc1 49 rawExtendHwMultiInsn [hdiv384]
  mc_step_ex_with step_rawExtendHwMulti hc1 50 rawExtendHwMultiInsn [u_b6_3]
  mc_step_ex_with step_rawExtendHwMulti hc1 51 rawExtendHwMultiInsn [u_cons]
  mc_step_ex_with step_rawExtendHwMulti hc1 52 rawExtendHwMultiInsn [hx20, u_rem]
  mc_step_ex step_rawExtendHwMulti hc1 53 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc1 54 rawExtendHwMultiInsn [hx19]
  mc_step_ex_with step_rawExtendHwMulti hc1 55 rawExtendHwMultiInsn [hx21]
  apply run_branch_call_at hb56
  dsimp only [setX_mk_r30]
  apply let_cur_state
  intro sCall
  have hsp_sub_eq : sCall.sp - 0x100 = orig.sp - 0x150 := sp_sub_0x50_sub_0x100 orig.sp
  have hrw_f6 : sCall.mem.isRWRange (sCall.sp - 0x100) 0x100 := by
    rw [hsp_sub_eq]
    exact isRWRange_sub d_full1.rwRange (by omega) (by omega)
  rcases hwFold6_mc_spec (s := sCall) (s_in := s_in) hs hb1 hsz6 hc1 hg1 hro rfl
      (by dsimp only [sCall]; omega) hrw_f6
      (by dsimp only [sCall, getW_mk_r0]; exact hw1) rfl rfl rfl with
    ⟨kF6, sF6, hrF6, hpcF6, hr0F6, d_f6, hcsF6⟩
  apply run_bind_exists hrF6
  rw [hsp_sub_eq] at d_f6
  have d_full2 : StackDelta code Layout orig.mem sF6.mem (orig.sp - 0x150) 0x150 :=
    d_full1.trans_sub d_f6 (by omega) (by omega)
  have hsaved2 : SavedFrameMulti sF6.mem (orig.sp - 0x50) orig :=
    hsaved.of_memOutsideEq d_f6.outside hb_sp0 (by omega)
  have hc2 := d_f6.codeLoaded
  have hg2 := d_f6.globalsLoaded
  have hro2 := d_f6.hasROBytes hro
  let s6 := Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + blocks6.toNat * 384))
  have hpcF6' : sF6.pc = Layout.rawExtendHwMultiBase + 228 :=
    hpcF6.trans (by dsimp only [sCall]; simp only [UInt64.add_assoc]; rfl)
  have hspF6  : sF6.sp = orig.sp - 0x50 := hcsF6.sp
  have hx19F6 : sF6.regs.x19 = objPtr := hcsF6.x19
  have hx20F6 : sF6.regs.x20 = ulen.toUInt64 := hcsF6.x20
  have hx21F6 : sF6.regs.x21 = uoff.toUInt64 := hcsF6.x21
  have hx23F6 : sF6.regs.x23 = 0xaaaaaaaaaaaaaaab := hcsF6.x23
  have hx24F6 : sF6.regs.x24 = consumed.toUInt64 := hcsF6.x24
  have hx25F6 : sF6.regs.x25 = rem.toUInt64 := hcsF6.x25
  have hx27F6 : sF6.regs.x27 = orig.regs.x27 := hcsF6.x27.trans hx27
  have hx28F6 : sF6.regs.x28 = orig.regs.x28 := hcsF6.x28.trans hx28
  have hd8F6  : sF6.getD r8  = orig.getD r8  := hcsF6.d8.trans hd8
  have hd9F6  : sF6.getD r9  = orig.getD r9  := hcsF6.d9.trans hd9
  have hd10F6 : sF6.getD r10 = orig.getD r10 := hcsF6.d10.trans hd10
  have hd11F6 : sF6.getD r11 = orig.getD r11 := hcsF6.d11.trans hd11
  have hd12F6 : sF6.getD r12 = orig.getD r12 := hcsF6.d12.trans hd12
  have hd13F6 : sF6.getD r13 = orig.getD r13 := hcsF6.d13.trans hd13
  have hd14F6 : sF6.getD r14 = orig.getD r14 := hcsF6.d14.trans hd14
  have hd15F6 : sF6.getD r15 = orig.getD r15 := hcsF6.d15.trans hd15
  rcases sF6 with ⟨regs2, sp2, simd2, nzcv2, pc2, mem2⟩
  dsimp only at d_full2 hsaved2 hc2 hg2 hro2 hpcF6' hspF6 hx19F6 hx20F6 hx21F6
  dsimp only at hx23F6 hx24F6 hx25F6 hx27F6 hx28F6
  dsimp only [getW_mk_r0] at hr0F6
  subst hpcF6' hspF6
  have hrem96_iff : ((0x5f : UInt64) < rem.toUInt64) ↔ (96 ≤ rem.toNat) := by
    change (95 : Nat) < rem.toUInt64.toNat ↔ _
    rw [USize.toNat_toUInt64]; omega
  mc_step_ex step_rawExtendHwMulti hc2 57 rawExtendHwMultiInsn
  mc_step_ex_with step_rawExtendHwMulti hc2 58 rawExtendHwMultiInsn [hx24F6, hx21F6, u_mid]
  mc_step_ex_with step_rawExtendHwMulti hc2 59 rawExtendHwMultiInsn [hx25F6]
  by_cases hrem96 : 96 ≤ rem.toNat
  · -- Subpath 2b (`96 ≤ rem < 384`): `idx 60` jumps to `idx 72..112` → `113..118`
    have hhi96 : (0x5f : UInt64) < rem.toUInt64 := hrem96_iff.mpr hrem96
    obtain ⟨rblocks, d_rblocks⟩ : ∃ v, v = rem / 48 := ⟨_, rfl⟩
    obtain ⟨rws, d_rws⟩ : ∃ v, v = rblocks * 2 := ⟨_, rfl⟩
    obtain ⟨rL, d_rL⟩ : ∃ v, v = rblocks * 16 := ⟨_, rfl⟩
    obtain ⟨rL2, d_rL2⟩ : ∃ v, v = 2 * rL := ⟨_, rfl⟩
    obtain ⟨rb3, d_rb3⟩ : ∃ v, v = rws + rblocks := ⟨_, rfl⟩
    obtain ⟨rL3, d_rL3⟩ : ∃ v, v = 3 * rL := ⟨_, rfl⟩
    obtain ⟨rstop, d_rstop⟩ : ∃ v, v = mid + rL := ⟨_, rfl⟩
    obtain ⟨rtail, d_rtail⟩ : ∃ v, v = mid + rL3 := ⟨_, rfl⟩
    have hrblocks : rblocks.toNat = rem.toNat / 48 := by
      rw [d_rblocks, USize.toNat_div, e48]
    have hrws : rws.toNat = rblocks.toNat * 2 := by
      rw [d_rws, USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
    have hrL : rL.toNat = rblocks.toNat * 16 := by
      rw [d_rL, USize.toNat_mul, e16]; exact Nat.mod_eq_of_lt (by omega)
    have hrL2 : rL2.toNat = 2 * rL.toNat := by
      rw [d_rL2, USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
    have hrb3 : rb3.toNat = rws.toNat + rblocks.toNat := by
      rw [d_rb3, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hrL3 : rL3.toNat = 3 * rL.toNat := by
      rw [d_rL3, USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
    have hrstop : rstop.toNat = mid.toNat + rL.toNat := by
      rw [d_rstop, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hrtail : rtail.toNat = mid.toNat + rL3.toNat := by
      rw [d_rtail, USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hmid8 : (mid + 8).toNat = mid.toNat + 8 := usize_add8_toNat mid (by omega)
    obtain ⟨rum9, drum9⟩ : ∃ v : UInt64,
        UInt64.ofNat ((rem.toUInt64.toNat * (0xaaaaaaaaaaaaaaab : UInt64).toNat) >>> 64) = v :=
      ⟨_, rfl⟩
    have hdiv48_rem : rum9 >>> (5 : Nat).toUInt64 = rblocks.toUInt64 := by
      rw [← drum9, d_rblocks]; exact umulh_div48 rem hrem_lt384
    have u_rws : rblocks.toUInt64 <<< (1 : Nat).toUInt64 = rws.toUInt64 :=
      lsl64_usize rblocks rws 1 (by decide) hrws
    have u_rL : rblocks.toUInt64 <<< (4 : Nat).toUInt64 = rL.toUInt64 :=
      lsl64_usize rblocks rL 4 (by decide) hrL
    have u_rL2 : rblocks.toUInt64 <<< (5 : Nat).toUInt64 = rL2.toUInt64 :=
      lsl64_usize rblocks rL2 5 (by decide) (by omega)
    have u_rb3 : rws.toUInt64 + rblocks.toUInt64 = rb3.toUInt64 := usize_add_u64 hrb3
    have u_rL3 : rb3.toUInt64 <<< (4 : Nat).toUInt64 = rL3.toUInt64 :=
      lsl64_usize rb3 rL3 4 (by decide) (by omega)
    have u_rstop : rL.toUInt64 + mid.toUInt64 = rstop.toUInt64 := usize_add_u64 (by omega)
    have u_mid8 : mid.toUInt64 + 8 = (mid + 8).toUInt64 := usize_add_lit_u64 hmid8
    have u_rtail : rL3.toUInt64 + mid.toUInt64 = rtail.toUInt64 := usize_add_u64 (by omega)
    have hnhs : ¬ (rstop.toUInt64 ≤ mid.toUInt64) := by
      intro hle64
      have : rstop.toUInt64.toNat ≤ mid.toUInt64.toNat := hle64
      rw [USize.toNat_toUInt64, USize.toNat_toUInt64] at this
      omega
    have hlt_rstop : mid < rstop := USize.lt_iff_toNat_lt.mpr (by omega)
    have hle_rf3 : mid.toNat ≤ rstop.toNat := by omega
    have hal_rf3 : (rstop.toNat - mid.toNat) % 16 = 0 := by omega
    have hrL_f3 : rstop.toNat + 2 * rL.toNat ≤ a.size := by omega
    obtain ⟨base, hbase⟩ : ∃ base : UInt64, objPtr + 0x18 = base := ⟨objPtr + 0x18, rfl⟩
    have hro_base : Arm64.Mem.hasROBytes mem2 base a := by rw [← hbase]; exact hro2
    have hbase_mid : objPtr + (mid.toUInt64 + 0x18) = base + mid.toUInt64 := by
      rw [← hbase, UInt64.add_comm mid.toUInt64 0x18, ← UInt64.add_assoc]
    mc_step_ex_with step_rawExtendHwMulti hc2 60 rawExtendHwMultiInsn [hhi96]
    mc_step_ex_with step_rawExtendHwMulti hc2 72 rawExtendHwMultiInsn [hx25F6, hx23F6, drum9]
    mc_step_ex_with step_rawExtendHwMulti hc2 73 rawExtendHwMultiInsn [hdiv48_rem]
    mc_step_ex_with step_rawExtendHwMulti hc2 74 rawExtendHwMultiInsn [u_rws]
    mc_step_ex_with step_rawExtendHwMulti hc2 75 rawExtendHwMultiInsn [u_rL]
    mc_step_ex_with step_rawExtendHwMulti hc2 76 rawExtendHwMultiInsn [u_rb3]
    mc_step_ex_with step_rawExtendHwMulti hc2 77 rawExtendHwMultiInsn [u_rL3]
    mc_step_ex_with step_rawExtendHwMulti hc2 78 rawExtendHwMultiInsn [u_rstop]
    mc_step_ex step_rawExtendHwMulti hc2 79 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc2 80 rawExtendHwMultiInsn [hnhs]
    mc_step_ex step_rawExtendHwMulti hc2 81 rawExtendHwMultiInsn
    mc_step_ex step_rawExtendHwMulti hc2 82 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc2 83 rawExtendHwMultiInsn [u_rL2]
    mc_step_ex_with step_rawExtendHwMulti hc2 84 rawExtendHwMultiInsn [hx19F6]
    mc_step_ex_with step_rawExtendHwMulti hc2 85 rawExtendHwMultiInsn [hx21F6, hx24F6, u_mid']
    mc_step_ex_with step_rawExtendHwMulti hc2 86 rawExtendHwMultiInsn [u_mid8]
    mc_step_ex_with step_rawExtendHwMulti hc2 87 rawExtendHwMultiInsn [hbase_mid]
    apply let_cur_state
    intro st0
    rcases rawExtendHwMulti_loop2 hs (by omega) hrL2 hrL_f3 (rstop.toNat - mid.toNat) st0 mid
        hle_rf3 hal_rf3 rfl hlt_rstop s6 0 0
        hc2 hg2 hro_base (by dsimp only [st0]; congr 1) rfl rfl rfl rfl rfl rfl
        (by dsimp only [st0, getW_mk_r8]; exact hr0F6)
        (by dsimp only [st0, getW_mk_r2]; rfl)
        (by dsimp only [st0, getW_mk_r3]; rfl) with
      ⟨kL2, stL2, hrL2_run, hpcL2, hr0L2, hmemL2, hkl2⟩
    apply run_bind_exists hrL2_run
    let rs3 := Crc32c.hwFold3 a hs mid rstop rws rL rL2 hle_rf3 hal_rf3 hrL2 hrL_f3 s6 0 0
    have hspL2  : stL2.sp = orig.sp - 0x50 := hkl2.sp
    have hx19L2 : stL2.regs.x19 = objPtr := hkl2.x19
    have hx20L2 : stL2.regs.x20 = ulen.toUInt64 := hkl2.x20.trans hx20F6
    have hx21L2 : stL2.regs.x21 = uoff.toUInt64 := hkl2.x21
    have hx22L2 : stL2.regs.x22 = mid.toUInt64 := hkl2.x22
    have hx23L2 : stL2.regs.x23 = rL3.toUInt64 := hkl2.x23
    have hx27L2 : stL2.regs.x27 = orig.regs.x27 := hkl2.x27.trans hx27F6
    have hx28L2 : stL2.regs.x28 = orig.regs.x28 := hkl2.x28.trans hx28F6
    have hd8L2  : stL2.getD r8  = orig.getD r8  := hkl2.d8.trans hd8F6
    have hd9L2  : stL2.getD r9  = orig.getD r9  := hkl2.d9.trans hd9F6
    have hd10L2 : stL2.getD r10 = orig.getD r10 := hkl2.d10.trans hd10F6
    have hd11L2 : stL2.getD r11 = orig.getD r11 := hkl2.d11.trans hd11F6
    have hd12L2 : stL2.getD r12 = orig.getD r12 := hkl2.d12.trans hd12F6
    have hd13L2 : stL2.getD r13 = orig.getD r13 := hkl2.d13.trans hd13F6
    have hd14L2 : stL2.getD r14 = orig.getD r14 := hkl2.d14.trans hd14F6
    have hd15L2 : stL2.getD r15 = orig.getD r15 := hkl2.d15.trans hd15F6
    rcases stL2 with ⟨regsL, spL, simdL, nzcvL, pcL, memL⟩
    dsimp only at hpcL2 hmemL2 hspL2 hx19L2 hx20L2 hx21L2 hx22L2 hx23L2 hx27L2 hx28L2
    dsimp only [getW_mk_r0] at hr0L2
    subst hpcL2 hmemL2
    mc_step_ex step_rawExtendHwMulti hc2 109 rawExtendHwMultiInsn
    mc_step_ex_with step_rawExtendHwMulti hc2 110 rawExtendHwMultiInsn [hx23L2, hx22L2, u_rtail]
    mc_step_ex_with step_rawExtendHwMulti hc2 111 rawExtendHwMultiInsn [hx20L2, hx21L2, u_fin]
    mc_step_ex_with step_rawExtendHwMulti hc2 112 rawExtendHwMultiInsn [hx19L2]
    apply let_cur_state
    intro stE
    rcases rawExtendHwMulti_epilogue_at113 (s := stE) (orig := orig) hs
        (tailI := rtail) (fin := fin) (by omega) (by omega) (acc := rs3)
        hc2 hro2 (by dsimp only [stE]; congr 1) hspL2 hsaved2 rfl rfl rfl
        (by dsimp only [stE, getW_mk_r3]; exact hr0L2)
        hx27L2 hx28L2 hd8L2 hd9L2 hd10L2 hd11L2 hd12L2 hd13L2 hd14L2 hd15L2 with
      ⟨kE, s', hrE, hpcE, hr0E, hmemE, hcsE⟩
    refine ⟨kE, s', hrE, hpcE, ?_, hmemE ▸ d_full2, hcsE⟩
    rw [hr0E]
    dsimp only [rs3]
    rw [hwFold3_tail_eq a hs mid rstop rws rL rL2 rtail fin
      (by omega) (by omega) hrL2 hrstop (by omega) hle_rf3 hal_rf3 hrL_f3 (by omega) (by omega) s6]
    dsimp only [s6]
    rw [hmid, hcons, hfin, ← Crc32c.rawExtend_append,
      Crc32c.bytes_append a (by omega) (by omega) hsz]
  · -- Subpath 2a (`rem < 96`): `idx 60..65` → `113..118`
    have hnhi96 : ¬ ((0x5f : UInt64) < rem.toUInt64) := fun h => hrem96 (hrem96_iff.mp h)
    mc_step_ex_with step_rawExtendHwMulti hc2 60 rawExtendHwMultiInsn [hnhi96]
    mc_step_ex_with step_rawExtendHwMulti hc2 61 rawExtendHwMultiInsn [hx20F6, hx21F6, u_fin]
    mc_step_ex_with step_rawExtendHwMulti hc2 62 rawExtendHwMultiInsn [hx19F6]
    mc_step_ex step_rawExtendHwMulti hc2 63 rawExtendHwMultiInsn
    mc_step_ex step_rawExtendHwMulti hc2 64 rawExtendHwMultiInsn
    mc_step_ex step_rawExtendHwMulti hc2 65 rawExtendHwMultiInsn
    apply let_cur_state
    intro stE
    rcases rawExtendHwMulti_epilogue_at113 (s := stE) (orig := orig) hs
        (tailI := mid) (fin := fin) (by omega) (by omega) (acc := s6)
        hc2 hro2 (by dsimp only [stE]; congr 1) rfl hsaved2 rfl rfl rfl
        (by dsimp only [stE, getW_mk_r3]; exact hr0F6)
        hx27F6 hx28F6 hd8F6 hd9F6 hd10F6 hd11F6 hd12F6 hd13F6 hd14F6 hd15F6 with
      ⟨kE, s', hrE, hpcE, hr0E, hmemE, hcsE⟩
    refine ⟨kE, s', hrE, hpcE, ?_, hmemE ▸ d_full2, hcsE⟩
    rw [hr0E]
    dsimp only [s6]
    rw [hmid, hcons, hfin, ← Crc32c.rawExtend_append,
      Crc32c.bytes_append a (by omega) (by omega) hsz]

/-! ### Section 6: Public machine-code specification for `_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg` -/

/-- Full machine-code specification of `_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg`
(`119` instructions, `Hw.c.o`):
from any state `s` at `Layout.rawExtendHwMultiBase` with `.rw` stack `[s.sp - 0x150, s.sp)`
(`336` bytes total, covering both `rawExtendHwMulti`'s `0x50` frame and `hwFold6`'s `0x100`
nested frame), `.ro` payload `a` at `objPtr + 0x18`, `W0 = s_in`, `X1 = objPtr`,
`X2 = uoff`, and `X3 = ulen` (`96 ≤ ulen`, `uoff + ulen ≤ a.size`), execution terminates
at `s.regs.x30` with:
- `W0 = Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + ulen.toNat))`
  (equal to `Crc32c.rawExtendHwMulti s_in a hs uoff ulen hsz h96`),
- `StackDelta code Layout s.mem s'.mem (s.sp - 0x150) 0x150` (preserving all `.ro` and
  unmapped guard-page bytes and all memory outside `[s.sp - 0x150, s.sp)`), and
- full AAPCS64 callee-saved preservation (`CalleeSaved s s'`). -/
theorem rawExtendHwMulti_mc_spec {code : UInt64 → Option UInt32} {Layout : CodeLayout}
    {s : Arm64.ArmState} {objPtr : UInt64} {a : ByteArray} (hs : a.size < USize.size)
    {uoff ulen : USize} (hsz : uoff.toNat + ulen.toNat ≤ a.size) (h96 : 96 ≤ ulen)
    {s_in : UInt32}
    (hc : CodeLoaded code s.mem Layout)
    (hg : GlobalsLoaded s.mem Layout)
    (hro : s.mem.hasROBytes (objPtr + 0x18) a)
    (hpc : s.pc = Layout.rawExtendHwMultiBase)
    (hsp_lo : 0x150 ≤ s.sp.toNat)
    (hrw : s.mem.isRWRange (s.sp - 0x150) 0x150)
    (hw0 : s.getW r0 = s_in)
    (hx1 : s.regs.x1 = objPtr)
    (hx2 : s.regs.x2 = uoff.toUInt64)
    (hx3 : s.regs.x3 = ulen.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend s_in (Crc32c.bytes a uoff.toNat (uoff.toNat + ulen.toNat)) ∧
      StackDelta code Layout s.mem s'.mem (s.sp - 0x150) 0x150 ∧
      CalleeSaved s s' := by
  have : UInt64.size = 2 ^ 64 := rfl
  have e96 : (96 : USize).toNat = 96 := by simp
  have e768 : (768 : USize).toNat = 768 := by simp
  have h96_nat : 96 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h96; omega
  have hsp_150 : (s.sp - 0x150).toNat = s.sp.toNat - 0x150 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x150 ≤ s.sp.toNat; omega)
  have hsp_50 : (s.sp - 0x50).toNat = s.sp.toNat - 0x50 :=
    UInt64.toNat_sub_of_le _ _ (by change 0x50 ≤ s.sp.toNat; omega)
  have hrw_50 : s.mem.isRWRange (s.sp - 0x50) 0x50 :=
    isRWRange_sub hrw (by omega) (by omega)
  have d_full0 := StackDelta.refl hrw hc hg
  rcases rawExtendHwMulti_prologue hc hg hpc hrw_50 hw0 hx1 hx2 hx3 with
    ⟨stP, hrP, hpcP, hspP, d_pro, hsavedP, hw1P, hx19P, hx21P, hx20P,
     hx27P, hx28P, hd8P, hd9P, hd10P, hd11P, hd12P, hd13P, hd14P, hd15P⟩
  apply run_bind_exists hrP
  have d_full1 : StackDelta code Layout s.mem stP.mem (s.sp - 0x150) 0x150 :=
    d_full0.trans_sub d_pro (by omega) (by omega)
  have hro1 : stP.mem.hasROBytes (objPtr + 0x18) a := d_full1.hasROBytes hro
  have hsaved1 : SavedFrameMulti stP.mem (s.sp - 0x50) s := hsavedP
  by_cases h768 : 768 ≤ ulen
  · have hpc768 : stP.pc = Layout.rawExtendHwMultiBase + 184 := by
      simpa [h768] using hpcP
    have h768_nat : 768 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h768; omega
    exact rawExtendHwMulti_path2 hs hsz h768_nat hsp_lo d_full1 d_pro.rwRange.1 hro1
      hpc768 hspP hsaved1 hw1P hx19P hx21P hx20P hx27P hx28P
      hd8P hd9P hd10P hd11P hd12P hd13P hd14P hd15P
  · have hpcLt : stP.pc = Layout.rawExtendHwMultiBase + 48 := by
      simpa [h768] using hpcP
    have hlt768 : ulen.toNat < 768 := by
      have : ¬ 768 ≤ ulen.toNat := fun h => h768 (USize.le_iff_toNat_le.mpr (by omega))
      omega
    rcases rawExtendHwMulti_path1 hs hsz h96_nat hlt768
        d_full1.codeLoaded d_full1.globalsLoaded hro1
        hpcLt hspP hsaved1 hw1P hx19P hx21P hx20P hx27P hx28P
        hd8P hd9P hd10P hd11P hd12P hd13P hd14P hd15P with
      ⟨k1, s', hr1, hpc1, hr0_1, hmem1, hcs1⟩
    exact ⟨k1, s', hr1, hpc1, hr0_1, hmem1 ▸ d_full1, hcs1⟩

end Crc32c.Arm64MC
