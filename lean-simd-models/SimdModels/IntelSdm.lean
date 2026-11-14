/-
Authoritative Intel SDM / Intel Intrinsics Guide cross-check for the x86-64
instruction models (`CRC32` and `PCLMULQDQ`).

Transcribed directly from Intel 64 and IA-32 Architectures Software Developer's
Manual, Vol. 2A (`CRC32 — Accumulate CRC32 Value`) and Vol. 2B (`PCLMULQDQ —
Carry-Less Multiplication Quadword`):
- `CRC32` bit-reflects `SRC` and `DEST[31:0]`, left-shifts them into a
  `(32 + size)`-bit window, XORs, reduces `MOD2 11EDC6F41H` (using the full
  33-bit generator `0x11EDC6F41`), bit-reflects the 32-bit remainder, and on
  64-bit `CRC32 r64, r/m64` zero-extends `DEST[63:32] := 0`.
- `PCLMULQDQ` selects `TEMP1` via `imm8[0]` and `TEMP2` via `imm8[4]` (ignoring
  bits `1..3` and `5..7` of `imm8`), computes bits `0..63` and `64..126` via
  discrete convolution XOR-AND loops, and sets `DEST[127] := 0`.

Rather than checking only a finite vector sample, this module proves universal
equality (`∀` inputs and `∀ imm8 : UInt8`) between Intel's SDM pseudocode and
`SimdModels.Model` in Lean's kernel using only Lean core (`Init`).
-/
import SimdModels.Models

namespace SimdModels.IntelSdm

/-! ### Bit helpers for `1 <<< idx` assembly -/

private theorem testBit_one_succ (m : Nat) : Nat.testBit 1 (m + 1) = false := by
  rw [Nat.testBit_succ]; simp

private theorem getLsbD_one_shiftLeft {w : Nat} (p i : Nat) (hi : i < w) :
    ((1#w) <<< p).getLsbD i = decide (i = p) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hip : i < p
  · have hne : i ≠ p := by omega
    simp [hip, hi, hne]
  · have h1 : (1#w).getLsbD (i - p) = decide (i - p = 0) := by
      cases hk : i - p with
      | zero => cases w with | zero => omega | succ w' => simp
      | succ m =>
        cases w with
        | zero => omega
        | succ w' => simp [BitVec.getLsbD, testBit_one_succ]
    simp only [hip, hi, decide_true, Bool.true_and, h1]
    by_cases heq : i = p
    · subst heq; simp
    · have : i - p ≠ 0 := by omega
      simp [heq, this]

/-! ### Intel SDM `BIT_REFLECT` and `MOD2 11EDC6F41H` (`CRC32`) -/

/-- Loop of Intel SDM `BIT_REFLECT`: sets `dst[w - 1 - k] := src[k]` for `k = 0 .. m - 1`. -/
def bitReflectLoop (w : Nat) (src : BitVec w) : Nat → BitVec w
  | 0 => 0
  | k + 1 =>
    let r := bitReflectLoop w src k
    if src.getLsbD k then r ||| (1#w <<< (w - 1 - k)) else r

/-- Intel SDM `BIT_REFLECT8` / `BIT_REFLECT16` / `BIT_REFLECT32` / `BIT_REFLECT64`. -/
def bitReflect (w : Nat) (src : BitVec w) : BitVec w :=
  bitReflectLoop w src w

private theorem bitReflectLoop_getLsbD (w : Nat) (src : BitVec w) (k : Nat) (hk : k ≤ w)
    (i : Nat) (hi : i < w) :
    (bitReflectLoop w src k).getLsbD i = (decide (w - 1 - i < k) && src.getLsbD (w - 1 - i)) := by
  induction k with
  | zero => simp [bitReflectLoop]
  | succ k ih =>
    simp only [bitReflectLoop]
    have ih' := ih (by omega)
    by_cases hs : src.getLsbD k = true
    · simp only [hs, ↓reduceIte, BitVec.getLsbD_or, ih', getLsbD_one_shiftLeft (w - 1 - k) i hi]
      by_cases hik : i = w - 1 - k
      · have hrev : w - 1 - i = k := by omega
        rw [decide_eq_true hik, hrev, hs]
        simp
      · have hlt : (w - 1 - i < k + 1) ↔ (w - 1 - i < k) := by omega
        simp [hik, hlt]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, ih']
      by_cases hrev : w - 1 - i = k
      · simp [hrev, hs]
      · have hlt : (w - 1 - i < k + 1) ↔ (w - 1 - i < k) := by omega
        simp [hlt]

theorem bitReflect_eq_reverse (w : Nat) (src : BitVec w) :
    bitReflect w src = src.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bitReflect, bitReflectLoop_getLsbD w src w (Nat.le_refl w) i hi,
    BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp [hi, show w - 1 - i < w by omega]

/-- Intel SDM's full 33-bit Castagnoli polynomial `11EDC6F41H`. -/
def crc32Divisor : BitVec 33 := 0x11EDC6F41#33

/-- Division loop of Intel SDM `TEMP5 MOD2 11EDC6F41H`, clearing bits from `n - 1` down to `32`. -/
def mod2Loop {n : Nat} : Nat → BitVec n → BitVec n
  | 0, data => data
  | k + 1, data =>
    mod2Loop k (if data.getLsbD (32 + k) then data ^^^ (crc32Divisor.setWidth n <<< k) else data)

/-- Intel SDM `MOD2 11EDC6F41H`. -/
def mod2 {n : Nat} (data : BitVec n) : BitVec 32 :=
  (mod2Loop (n - 32) data).setWidth 32

private theorem crc32Divisor_low32 (j : Nat) (hj : j < 32) :
    crc32Divisor.getLsbD j = Model.crc32cPoly.getLsbD j := by
  have h : crc32Divisor.setWidth 32 = Model.crc32cPoly := by decide
  rw [← h, BitVec.getLsbD_setWidth]
  simp [hj]

private theorem mod2Loop_eq_poly32Mod2Loop {n : Nat} (k : Nat) (d1 d2 : BitVec n)
    (h : d1.setWidth (32 + k) = d2.setWidth (32 + k)) :
    (mod2Loop k d1).setWidth 32 = (Model.poly32Mod2Loop Model.crc32cPoly k d2).setWidth 32 := by
  induction k generalizing d1 d2 with
  | zero => exact h
  | succ k ih =>
    simp only [mod2Loop, Model.poly32Mod2Loop]
    have hbit : d1.getLsbD (32 + k) = d2.getLsbD (32 + k) := by
      have := congrArg (fun v => v.getLsbD (32 + k)) h
      simpa [BitVec.getLsbD_setWidth, show 32 + k < 32 + (k + 1) by omega] using this
    rw [hbit]
    apply ih
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h_low : d1.getLsbD i = d2.getLsbD i := by
      have := congrArg (fun v => v.getLsbD i) h
      simpa [BitVec.getLsbD_setWidth, show i < 32 + (k + 1) by omega] using this
    by_cases hb : d2.getLsbD (32 + k) = true
    · simp only [hb, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor,
        BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, h_low]
      by_cases hik : i < k
      · simp [hik]
      · by_cases hin : i < n
        · simp [hik, hin, crc32Divisor_low32 (i - k) (by omega)]
        · simp [hik, hin]
    · simp [hb, hi, h_low]

theorem mod2_eq_poly32Mod2 {n : Nat} (data : BitVec n) :
    mod2 data = Model.poly32Mod2 data Model.crc32cPoly :=
  mod2Loop_eq_poly32Mod2Loop (n - 32) data data rfl

private theorem shift_xor_eq_append_xor (size : Nat) (acc : BitVec 32) (val : BitVec size) :
    let temp1 := bitReflect size val
    let temp2 := bitReflect 32 acc
    let w := 32 + size
    (temp1.setWidth w <<< 32) ^^^ (temp2.setWidth w <<< size) =
      (acc.reverse ++ (0 : BitVec size)) ^^^
        ((val.reverse ++ (0 : BitVec 32)).cast (Nat.add_comm size 32)) := by
  simp only [bitReflect_eq_reverse]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_cast, hi, decide_true, Bool.true_and]
  by_cases h32 : i < 32
  · by_cases hs : i < size
    · simp [h32, hs]
    · simp [h32, hs, show i - size < 32 + size by omega]
  · by_cases hs : i < size
    · simp [h32, hs, show i - 32 < 32 + size by omega]
    · simp [h32, hs, show i - 32 < 32 + size by omega, show i - size < 32 + size by omega,
        Bool.xor_comm]

/-- Intel SDM `CRC32 r32, r/m8` (`_mm_crc32_u8`). -/
def crc32_u8 (dest : UInt32) (src : UInt8) : UInt32 :=
  let temp1 : BitVec 8  := bitReflect 8 src.toBitVec
  let temp2 : BitVec 32 := bitReflect 32 dest.toBitVec
  let temp3 : BitVec 40 := temp1.setWidth 40 <<< 32
  let temp4 : BitVec 40 := temp2.setWidth 40 <<< 8
  let temp5 : BitVec 40 := temp3 ^^^ temp4
  let temp6 : BitVec 32 := mod2 temp5
  ⟨bitReflect 32 temp6⟩

/-- Intel SDM `CRC32 r32, r/m16` (`_mm_crc32_u16`). -/
def crc32_u16 (dest : UInt32) (src : UInt16) : UInt32 :=
  let temp1 : BitVec 16 := bitReflect 16 src.toBitVec
  let temp2 : BitVec 32 := bitReflect 32 dest.toBitVec
  let temp3 : BitVec 48 := temp1.setWidth 48 <<< 32
  let temp4 : BitVec 48 := temp2.setWidth 48 <<< 16
  let temp5 : BitVec 48 := temp3 ^^^ temp4
  let temp6 : BitVec 32 := mod2 temp5
  ⟨bitReflect 32 temp6⟩

/-- Intel SDM `CRC32 r32, r/m32` (`_mm_crc32_u32`). -/
def crc32_u32 (dest : UInt32) (src : UInt32) : UInt32 :=
  let temp1 : BitVec 32 := bitReflect 32 src.toBitVec
  let temp2 : BitVec 32 := bitReflect 32 dest.toBitVec
  let temp3 : BitVec 64 := temp1.setWidth 64 <<< 32
  let temp4 : BitVec 64 := temp2.setWidth 64 <<< 32
  let temp5 : BitVec 64 := temp3 ^^^ temp4
  let temp6 : BitVec 32 := mod2 temp5
  ⟨bitReflect 32 temp6⟩

/-- Intel SDM `CRC32 r64, r/m64` (`_mm_crc32_u64`): reads `DEST[31:0]` and
zero-extends `DEST[63:32] := 00000000H`. -/
def crc32_r64 (dest : UInt64) (src : UInt64) : UInt64 :=
  let temp1 : BitVec 64 := bitReflect 64 src.toBitVec
  let temp2 : BitVec 32 := bitReflect 32 (dest.toBitVec.setWidth 32)
  let temp3 : BitVec 96 := temp1.setWidth 96 <<< 32
  let temp4 : BitVec 96 := temp2.setWidth 96 <<< 64
  let temp5 : BitVec 96 := temp3 ^^^ temp4
  let temp6 : BitVec 32 := mod2 temp5
  ⟨(0 : BitVec 32) ++ bitReflect 32 temp6⟩

/-- The `UInt32` binding view `(uint32_t)_mm_crc32_u64(c, v)`. -/
def crc32_u64 (c : UInt32) (v : UInt64) : UInt32 :=
  (crc32_r64 c.toUInt64 v).toUInt32

theorem crc32_u8_eq (c : UInt32) (v : UInt8) :
    crc32_u8 c v = Model.crc32c_u8 c v := by
  simp only [crc32_u8, Model.crc32c_u8, Model.crc32c]
  congr 1
  rw [bitReflect_eq_reverse, mod2_eq_poly32Mod2, shift_xor_eq_append_xor 8 c.toBitVec v.toBitVec]

theorem crc32_u16_eq (c : UInt32) (v : UInt16) :
    crc32_u16 c v = Model.crc32c_u16 c v := by
  simp only [crc32_u16, Model.crc32c_u16, Model.crc32c]
  congr 1
  rw [bitReflect_eq_reverse, mod2_eq_poly32Mod2, shift_xor_eq_append_xor 16 c.toBitVec v.toBitVec]

theorem crc32_u32_eq (c : UInt32) (v : UInt32) :
    crc32_u32 c v = Model.crc32c_u32 c v := by
  simp only [crc32_u32, Model.crc32c_u32, Model.crc32c]
  congr 1
  rw [bitReflect_eq_reverse, mod2_eq_poly32Mod2, shift_xor_eq_append_xor 32 c.toBitVec v.toBitVec]

theorem crc32_r64_eq (dest src : UInt64) :
    crc32_r64 dest src = (Model.crc32c_u64 dest.toUInt32 src).toUInt64 := by
  rw [← UInt64.toBitVec_inj]
  have hd : dest.toBitVec.setWidth 32 = dest.toUInt32.toBitVec := by simp
  have core : bitReflect 32 (mod2 ((bitReflect 64 src.toBitVec).setWidth 96 <<< 32 ^^^
      (bitReflect 32 dest.toUInt32.toBitVec).setWidth 96 <<< 64)) =
      Model.crc32c 64 dest.toUInt32.toBitVec src.toBitVec := by
    rw [bitReflect_eq_reverse, mod2_eq_poly32Mod2,
      shift_xor_eq_append_xor 64 dest.toUInt32.toBitVec src.toBitVec]
    rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [crc32_r64, hd, core, Model.crc32c_u64, UInt32.toBitVec_toUInt64]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h32 : i < 32
  · simp [h32]
  · have hge : 32 ≤ i := by omega
    rw [BitVec.getLsbD_of_ge (Model.crc32c 64 dest.toUInt32.toBitVec src.toBitVec) i hge]
    simp [h32]

theorem crc32_u64_eq (c : UInt32) (v : UInt64) :
    crc32_u64 c v = Model.crc32c_u64 c v := by
  have hc : c.toUInt64.toUInt32 = c := by
    rw [← UInt32.toBitVec_inj]; simp
  rw [crc32_u64, crc32_r64_eq, hc]
  rw [← UInt32.toBitVec_inj]; simp

/-! ### Intel SDM `PCLMULQDQ` (`_mm_clmulepi64_si128`)

Intel SDM Vol. 2B Operation:

    IF (Imm8[0] = 0) THEN TEMP1 := SRC1.qword[0]; ELSE TEMP1 := SRC1.qword[1]; FI
    IF (Imm8[4] = 0) THEN TEMP2 := SRC2.qword[0]; ELSE TEMP2 := SRC2.qword[1]; FI
    For i = 0 to 63 {
        TmpB[i] := (TEMP1[0] and TEMP2[i]);
        For j = 1 to i {
            TmpB[i] := TmpB[i] xor (TEMP1[j] and TEMP2[i - j])
        }
        DEST[i] := TmpB[i];
    }
    For i = 64 to 126 {
        TmpB[i] := 0;
        For j = i - 63 to 63 {
            TmpB[i] := TmpB[i] xor (TEMP1[j] and TEMP2[i - j])
        }
        DEST[i] := TmpB[i];
    }
    DEST[127] := 0;
-/

/-- Inner `j`-loop of Intel SDM `PCLMULQDQ` for `0 ≤ i ≤ 63`: starts at
`TEMP1[0] and TEMP2[i]` and XORs `TEMP1[j] and TEMP2[i - j]` for `j = 1 .. m`. -/
def pclmulLowInner (temp1 temp2 : BitVec 64) (i : Nat) : Nat → Bool
  | 0 => temp1.getLsbD 0 && temp2.getLsbD i
  | j + 1 => xor (pclmulLowInner temp1 temp2 i j) (temp1.getLsbD (j + 1) && temp2.getLsbD (i - (j + 1)))

/-- Inner `j`-loop of Intel SDM `PCLMULQDQ` for `64 ≤ i ≤ 126`: starts at `0`
and XORs `TEMP1[j] and TEMP2[i - j]` for `j = start .. start + cnt - 1`. -/
def pclmulHighInner (temp1 temp2 : BitVec 64) (i start : Nat) : Nat → Bool
  | 0 => false
  | m + 1 =>
    let j := start + m
    xor (pclmulHighInner temp1 temp2 i start m) (temp1.getLsbD j && temp2.getLsbD (i - j))

/-- Outer `i = 0 .. 63` loop of Intel SDM `PCLMULQDQ`. -/
def pclmulLowLoop (temp1 temp2 : BitVec 64) : Nat → V128
  | 0 => 0
  | i + 1 =>
    let dest := pclmulLowLoop temp1 temp2 i
    if pclmulLowInner temp1 temp2 i i then dest ||| (1#128 <<< i) else dest

/-- Outer `i = 64 .. 126` loop of Intel SDM `PCLMULQDQ` (`cnt` steps starting at `64`). -/
def pclmulHighLoop (temp1 temp2 : BitVec 64) : Nat → V128 → V128
  | 0, dest => dest
  | m + 1, dest =>
    let dest' := pclmulHighLoop temp1 temp2 m dest
    let i := 64 + m
    if pclmulHighInner temp1 temp2 i (i - 63) (64 - (i - 63)) then
      dest' ||| (1#128 <<< i)
    else
      dest'

/-- Core 64x64 -> 128 carry-less multiplication from Intel SDM `PCLMULQDQ`
(`DEST[127] := 0` holds because neither `0..63` nor `64..126` sets bit 127). -/
def pclmul128 (temp1 temp2 : BitVec 64) : V128 :=
  pclmulHighLoop temp1 temp2 63 (pclmulLowLoop temp1 temp2 64)

/-- Full Intel SDM `PCLMULQDQ` (`_mm_clmulepi64_si128`). -/
def clmulepi64 (src1 src2 : V128) (imm8 : UInt8) : V128 :=
  let temp1 := if imm8.toBitVec.getLsbD 0 == false then (V128.lo64 src1).toBitVec else (V128.hi64 src1).toBitVec
  let temp2 := if imm8.toBitVec.getLsbD 4 == false then (V128.lo64 src2).toBitVec else (V128.hi64 src2).toBitVec
  pclmul128 temp1 temp2

private theorem pclmulLowLoop_getLsbD (t1 t2 : BitVec 64) (n i : Nat) (hn : n ≤ 64) (hi : i < 128) :
    (pclmulLowLoop t1 t2 n).getLsbD i = (decide (i < n) && pclmulLowInner t1 t2 i i) := by
  induction n with
  | zero => simp [pclmulLowLoop]
  | succ n ih =>
    simp only [pclmulLowLoop]
    have ih' := ih (by omega)
    by_cases hb : pclmulLowInner t1 t2 n n = true
    · simp only [hb, ↓reduceIte, BitVec.getLsbD_or, ih', getLsbD_one_shiftLeft n i hi]
      by_cases hin : i = n
      · subst hin; simp [hb]
      · have hlt : (i < n + 1) ↔ (i < n) := by omega
        simp [hin, hlt]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, ih']
      by_cases hin : i = n
      · subst hin; simp [hb]
      · have hlt : (i < n + 1) ↔ (i < n) := by omega
        simp [hlt]

private theorem pclmulHighLoop_getLsbD (t1 t2 : BitVec 64) (m : Nat) (hm : m ≤ 63) (base : V128)
    (i : Nat) (hi : i < 128) :
    (pclmulHighLoop t1 t2 m base).getLsbD i =
      (base.getLsbD i || (decide (64 ≤ i ∧ i < 64 + m) &&
        pclmulHighInner t1 t2 i (i - 63) (64 - (i - 63)))) := by
  induction m with
  | zero =>
    have : ¬ (64 ≤ i ∧ i < 64) := by omega
    simp [pclmulHighLoop, this]
  | succ m ih =>
    simp only [pclmulHighLoop]
    have ih' := ih (by omega)
    by_cases hb : pclmulHighInner t1 t2 (64 + m) (64 + m - 63) (64 - (64 + m - 63)) = true
    · simp only [hb, ↓reduceIte, BitVec.getLsbD_or, ih', getLsbD_one_shiftLeft (64 + m) i hi]
      by_cases him : i = 64 + m
      · subst him
        have hr : 64 ≤ 64 + m ∧ 64 + m < 64 + (m + 1) := by omega
        simp [hr, hb]
      · have hlt : (64 ≤ i ∧ i < 64 + (m + 1)) ↔ (64 ≤ i ∧ i < 64 + m) := by omega
        simp [him, hlt]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, ih']
      by_cases him : i = 64 + m
      · subst him
        have h2 : 64 ≤ 64 + m ∧ 64 + m < 64 + (m + 1) := by omega
        simp [h2, hb]
      · have hlt : (64 ≤ i ∧ i < 64 + (m + 1)) ↔ (64 ≤ i ∧ i < 64 + m) := by omega
        simp [hlt]

private theorem polynomialMultLoop_step_getLsbD (t1 t2 : BitVec 64) (k i : Nat) (hi : i < 128) :
    (Model.polynomialMultLoop t1 (t2.setWidth 128) (k + 1)).getLsbD i =
      xor ((Model.polynomialMultLoop t1 (t2.setWidth 128) k).getLsbD i)
        (decide (k ≤ i) && t1.getLsbD k && t2.getLsbD (i - k)) := by
  simp only [Model.polynomialMultLoop]
  by_cases h1 : t1.getLsbD k = true
  · simp only [h1, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases hik : i < k
    · have hle : ¬ k ≤ i := by omega
      simp [hik, hle]
    · have hle : k ≤ i := by omega
      simp [hik, hle, show i - k < 128 by omega]
  · simp [h1]

private theorem polynomialMultLoop_low_prefix (t1 t2 : BitVec 64) (i j : Nat)
    (hi : i < 64) (hj : j ≤ i) :
    (Model.polynomialMultLoop t1 (t2.setWidth 128) (j + 1)).getLsbD i =
      pclmulLowInner t1 t2 i j := by
  induction j with
  | zero =>
    rw [polynomialMultLoop_step_getLsbD t1 t2 0 i (by omega)]
    simp [Model.polynomialMultLoop, pclmulLowInner]
  | succ j ih =>
    rw [polynomialMultLoop_step_getLsbD t1 t2 (j + 1) i (by omega), ih (by omega), pclmulLowInner]
    simp [hj]

private theorem polynomialMultLoop_low_tail (t1 t2 : BitVec 64) (i d : Nat) (hi : i < 64) :
    (Model.polynomialMultLoop t1 (t2.setWidth 128) (i + 1 + d)).getLsbD i =
      (Model.polynomialMultLoop t1 (t2.setWidth 128) (i + 1)).getLsbD i := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show i + 1 + (d + 1) = (i + 1 + d) + 1 by omega,
      polynomialMultLoop_step_getLsbD t1 t2 (i + 1 + d) i (by omega), ih]
    have hle : ¬ (i + 1 + d ≤ i) := by omega
    simp [hle]

private theorem polynomialMultLoop_zero_before (t1 t2 : BitVec 64) (i k : Nat)
    (hi : i < 128) (hk : 64 + k ≤ i + 1) :
    (Model.polynomialMultLoop t1 (t2.setWidth 128) k).getLsbD i = false := by
  induction k with
  | zero => simp [Model.polynomialMultLoop]
  | succ k ih =>
    rw [polynomialMultLoop_step_getLsbD t1 t2 k i hi, ih (by omega),
      BitVec.getLsbD_of_ge t2 (i - k) (by omega)]
    simp

private theorem polynomialMultLoop_high_window (t1 t2 : BitVec 64) (i m : Nat)
    (hi64 : 64 ≤ i) (hi127 : i < 127) (hm : m ≤ 64 - (i - 63)) :
    (Model.polynomialMultLoop t1 (t2.setWidth 128) ((i - 63) + m)).getLsbD i =
      pclmulHighInner t1 t2 i (i - 63) m := by
  induction m with
  | zero =>
    simp [pclmulHighInner, polynomialMultLoop_zero_before t1 t2 i (i - 63) (by omega) (by omega)]
  | succ m ih =>
    rw [show (i - 63) + (m + 1) = ((i - 63) + m) + 1 by omega,
      polynomialMultLoop_step_getLsbD t1 t2 ((i - 63) + m) i (by omega), ih (by omega),
      pclmulHighInner]
    have hle : (i - 63) + m ≤ i := by omega
    simp [hle]

/-- Universal equivalence between Intel SDM `PCLMULQDQ`'s core convolution and
Arm ASL `PolynomialMult` over all `2^128` input pairs. -/
theorem pclmul128_eq_polynomialMult (temp1 temp2 : BitVec 64) :
    pclmul128 temp1 temp2 = Model.polynomialMult temp1 temp2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [pclmul128, pclmulHighLoop_getLsbD temp1 temp2 63 (by omega) _ i hi,
    pclmulLowLoop_getLsbD temp1 temp2 64 i (by omega) hi, Model.polynomialMult]
  by_cases h64 : i < 64
  · have hnr : ¬ (64 ≤ i ∧ i < 64 + 63) := by omega
    simp only [h64, decide_true, Bool.true_and, hnr, decide_false, Bool.false_and, Bool.or_false]
    have htail := polynomialMultLoop_low_tail temp1 temp2 i (63 - i) h64
    rw [show i + 1 + (63 - i) = 64 by omega] at htail
    rw [htail, polynomialMultLoop_low_prefix temp1 temp2 i i h64 (Nat.le_refl i)]
  · by_cases h127 : i < 127
    · have hr : 64 ≤ i ∧ i < 64 + 63 := by omega
      rw [decide_eq_false h64, decide_eq_true hr]
      simp only [Bool.false_and, Bool.false_or, Bool.true_and]
      have hwin := polynomialMultLoop_high_window temp1 temp2 i (64 - (i - 63))
        (by omega) h127 (Nat.le_refl _)
      rw [show (i - 63) + (64 - (i - 63)) = 64 by omega] at hwin
      exact hwin.symm
    · have hi127 : i = 127 := by omega
      subst hi127
      have hnr : ¬ (64 ≤ 127 ∧ 127 < 64 + 63) := by omega
      rw [decide_eq_false h64, decide_eq_false hnr,
        polynomialMultLoop_zero_before temp1 temp2 127 64 (by omega) (by omega)]
      rfl

/-- Universal equivalence between Intel SDM `PCLMULQDQ` (`_mm_clmulepi64_si128`)
and `SimdModels.Model.clmulepi64` for all `2^264` `(src1, src2, imm8)` triples. -/
theorem clmulepi64_eq (src1 src2 : V128) (imm8 : UInt8) :
    clmulepi64 src1 src2 imm8 = Model.clmulepi64 src1 src2 imm8 := by
  simp only [clmulepi64, Model.clmulepi64, pclmul128_eq_polynomialMult]
  cases imm8.toBitVec.getLsbD 0 <;> cases imm8.toBitVec.getLsbD 4 <;> rfl

private theorem setWidth64_ofHalves (x : UInt64) :
    (V128.ofHalves x 0).setWidth 64 = x.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [V128.ofHalves, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true,
    Bool.true_and, ↓reduceIte]

theorem clmulLo_eq_intel (a b : UInt64) :
    V128.lo64 (clmulepi64 (V128.ofHalves a 0) (V128.ofHalves b 0) 0x00) = Model.clmulLo a b := by
  rw [clmulepi64_eq]
  have hb0 : (0x00 : UInt8).toBitVec.getLsbD 0 = false := by decide
  have hb4 : (0x00 : UInt8).toBitVec.getLsbD 4 = false := by decide
  simp only [Model.clmulepi64, hb0, hb4, Bool.false_eq_true, ↓reduceIte, V128.lo64,
    setWidth64_ofHalves, Model.clmulLo]

theorem clmulHi_eq_intel (a b : UInt64) :
    V128.hi64 (clmulepi64 (V128.ofHalves a 0) (V128.ofHalves b 0) 0x00) = Model.clmulHi a b := by
  rw [clmulepi64_eq]
  have hb0 : (0x00 : UInt8).toBitVec.getLsbD 0 = false := by decide
  have hb4 : (0x00 : UInt8).toBitVec.getLsbD 4 = false := by decide
  simp only [Model.clmulepi64, hb0, hb4, Bool.false_eq_true, ↓reduceIte, V128.lo64, V128.hi64,
    setWidth64_ofHalves, Model.clmulHi]

end SimdModels.IntelSdm
