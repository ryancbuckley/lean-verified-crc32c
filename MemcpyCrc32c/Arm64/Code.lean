/-
Exact AArch64 (A64) Mach-O machine-code and relocation specification for all 7
reachable hardware CRC32C functions compiled from `MemcpyCrc32c.Impl.Hw` and
`MemcpyCrc32c.Impl.HwCombine` (`1,137` 32-bit instruction words total):

1. `_lp_leancrc32c_Crc32c_combine3` (`44` insns)
2. `_lp_leancrc32c_Crc32c_combine6` (`65` insns)
3. `_lp_leancrc32c_Crc32c_hwLoop___redArg` (`99` insns)
4. `_lp_leancrc32c_Crc32c_hwFold6Loop___redArg` (`197` insns)
5. `_lp_leancrc32c_Crc32c_hwFold6___redArg` (`186` insns)
6. `_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg` (`119` insns)
7. `_lp_leancrc32c_Crc32c_extendHwRaw___redArg` (`427` insns)

Verified byte-for-byte against `Hw.c.o`, `HwCombine.c.o`, `libleancrc32c.a`, and
the linked `test_c_abi` executable by `scripts/check_aarch64_mc.py`.
-/
import SimdModels.Arm64Lemmas
import MemcpyCrc32c.Impl.Hw

namespace Crc32c.Arm64MC
open SimdModels

/-! ### Fixed-width register, condition, and lane index constants -/

abbrev r0 : Arm64.RegIdx := ⟨0, by decide⟩
abbrev r1 : Arm64.RegIdx := ⟨1, by decide⟩
abbrev r2 : Arm64.RegIdx := ⟨2, by decide⟩
abbrev r3 : Arm64.RegIdx := ⟨3, by decide⟩
abbrev r4 : Arm64.RegIdx := ⟨4, by decide⟩
abbrev r5 : Arm64.RegIdx := ⟨5, by decide⟩
abbrev r6 : Arm64.RegIdx := ⟨6, by decide⟩
abbrev r7 : Arm64.RegIdx := ⟨7, by decide⟩
abbrev r8 : Arm64.RegIdx := ⟨8, by decide⟩
abbrev r9 : Arm64.RegIdx := ⟨9, by decide⟩
abbrev r10 : Arm64.RegIdx := ⟨10, by decide⟩
abbrev r11 : Arm64.RegIdx := ⟨11, by decide⟩
abbrev r12 : Arm64.RegIdx := ⟨12, by decide⟩
abbrev r13 : Arm64.RegIdx := ⟨13, by decide⟩
abbrev r14 : Arm64.RegIdx := ⟨14, by decide⟩
abbrev r15 : Arm64.RegIdx := ⟨15, by decide⟩
abbrev r16 : Arm64.RegIdx := ⟨16, by decide⟩
abbrev r17 : Arm64.RegIdx := ⟨17, by decide⟩
abbrev r18 : Arm64.RegIdx := ⟨18, by decide⟩
abbrev r19 : Arm64.RegIdx := ⟨19, by decide⟩
abbrev r20 : Arm64.RegIdx := ⟨20, by decide⟩
abbrev r21 : Arm64.RegIdx := ⟨21, by decide⟩
abbrev r22 : Arm64.RegIdx := ⟨22, by decide⟩
abbrev r23 : Arm64.RegIdx := ⟨23, by decide⟩
abbrev r24 : Arm64.RegIdx := ⟨24, by decide⟩
abbrev r25 : Arm64.RegIdx := ⟨25, by decide⟩
abbrev r26 : Arm64.RegIdx := ⟨26, by decide⟩
abbrev r27 : Arm64.RegIdx := ⟨27, by decide⟩
abbrev r28 : Arm64.RegIdx := ⟨28, by decide⟩
abbrev r29 : Arm64.RegIdx := ⟨29, by decide⟩
abbrev r30 : Arm64.RegIdx := ⟨30, by decide⟩
abbrev r31 : Arm64.RegIdx := ⟨31, by decide⟩
abbrev c0 : Fin 16 := ⟨0, by decide⟩
abbrev c1 : Fin 16 := ⟨1, by decide⟩
abbrev c2 : Fin 16 := ⟨2, by decide⟩
abbrev c3 : Fin 16 := ⟨3, by decide⟩
abbrev c4 : Fin 16 := ⟨4, by decide⟩
abbrev c5 : Fin 16 := ⟨5, by decide⟩
abbrev c6 : Fin 16 := ⟨6, by decide⟩
abbrev c7 : Fin 16 := ⟨7, by decide⟩
abbrev c8 : Fin 16 := ⟨8, by decide⟩
abbrev c9 : Fin 16 := ⟨9, by decide⟩
abbrev c10 : Fin 16 := ⟨10, by decide⟩
abbrev c11 : Fin 16 := ⟨11, by decide⟩
abbrev c12 : Fin 16 := ⟨12, by decide⟩
abbrev c13 : Fin 16 := ⟨13, by decide⟩
abbrev c14 : Fin 16 := ⟨14, by decide⟩
abbrev c15 : Fin 16 := ⟨15, by decide⟩
abbrev l0 : Fin 2 := ⟨0, by decide⟩
abbrev l1 : Fin 2 := ⟨1, by decide⟩

/-! ### Symbol identifiers, layout, and Mach-O relocation records -/

/-- Relocation target symbols referenced across `Hw.c.o` and `HwCombine.c.o`. -/
inductive SymId where
  | fnCombine3
  | fnCombine6
  | fnHwLoop
  | fnHwFold6Loop
  | fnHwFold6
  | fnRawExtendHwMulti
  | fnExtendHwRaw
  | gHwOne
  | gHwX64
  | gHwShiftSmallBytes
  | gKFold128_1
  | gKFold128_2
  | gKFold256_1
  | gKFold256_2
  | gKFold384_1
  | gKFold384_2
  | gKFold512_1
  | gKFold512_2
  deriving DecidableEq, Repr

/-- Linked virtual addresses of the 7 verified functions, the 11 module-level
constants/tables, and the runtime `ByteArray` object backing `hwShiftSmallBytes`. -/
structure CodeLayout where
  combine3Base         : UInt64
  combine6Base         : UInt64
  hwLoopBase           : UInt64
  hwFold6LoopBase      : UInt64
  hwFold6Base          : UInt64
  rawExtendHwMultiBase : UInt64
  extendHwRawBase      : UInt64
  hwOneAddr            : UInt64
  hwX64Addr            : UInt64
  hwShiftSmallAddr     : UInt64
  tblObjAddr           : UInt64
  kFold128_1Addr       : UInt64
  kFold128_2Addr       : UInt64
  kFold256_1Addr       : UInt64
  kFold256_2Addr       : UInt64
  kFold384_1Addr       : UInt64
  kFold384_2Addr       : UInt64
  kFold512_1Addr       : UInt64
  kFold512_2Addr       : UInt64
  deriving DecidableEq, Repr

/-- Resolve a `SymId` to its virtual address in `L`. -/
def CodeLayout.symAddr (L : CodeLayout) : SymId → UInt64
  | .fnCombine3         => L.combine3Base
  | .fnCombine6         => L.combine6Base
  | .fnHwLoop           => L.hwLoopBase
  | .fnHwFold6Loop      => L.hwFold6LoopBase
  | .fnHwFold6          => L.hwFold6Base
  | .fnRawExtendHwMulti => L.rawExtendHwMultiBase
  | .fnExtendHwRaw      => L.extendHwRawBase
  | .gHwOne             => L.hwOneAddr
  | .gHwX64             => L.hwX64Addr
  | .gHwShiftSmallBytes => L.hwShiftSmallAddr
  | .gKFold128_1        => L.kFold128_1Addr
  | .gKFold128_2        => L.kFold128_2Addr
  | .gKFold256_1        => L.kFold256_1Addr
  | .gKFold256_2        => L.kFold256_2Addr
  | .gKFold384_1        => L.kFold384_1Addr
  | .gKFold384_2        => L.kFold384_2Addr
  | .gKFold512_1        => L.kFold512_1Addr
  | .gKFold512_2        => L.kFold512_2Addr

/-- Concrete layout witness extracted from the linked `build/cxx/test_c_abi` binary. -/
def CodeLayout.testCAbiExample : CodeLayout where
  combine3Base         := 0x10000ee18
  combine6Base         := 0x10000f084
  hwLoopBase           := 0x1000140a4
  hwFold6LoopBase      := 0x100015064
  hwFold6Base          := 0x1000163c4
  rawExtendHwMultiBase := 0x1000168e0
  extendHwRawBase      := 0x100017e80
  hwOneAddr            := 0x10002428c
  hwX64Addr            := 0x10002429c
  hwShiftSmallAddr     := 0x100024290
  tblObjAddr           := 0x200000000
  kFold128_1Addr       := 0x1000242a0
  kFold128_2Addr       := 0x1000242a8
  kFold256_1Addr       := 0x1000242b0
  kFold256_2Addr       := 0x1000242b8
  kFold384_1Addr       := 0x1000242c0
  kFold384_2Addr       := 0x1000242c8
  kFold512_1Addr       := 0x1000242d0
  kFold512_2Addr       := 0x1000242d8

/-- Mach-O `ARM64_RELOC_BRANCH26` record at 32-bit instruction index `idx`. -/
structure BranchReloc where
  idx    : Nat
  isCall : Bool
  target : SymId
  deriving DecidableEq, Repr

/-- Mach-O `ARM64_RELOC_GOT_LOAD_PAGE21` + `PAGEOFF12` pair at `idx, idx + 1`. -/
structure GotReloc where
  idx    : Nat
  rd     : Arm64.RegIdx
  target : SymId
  deriving DecidableEq, Repr

/-- Linked `BL` (`isCall = true`) or `B` (`isCall = false`) at `pc` targeting `calleeBase`. -/
def BranchAt (code : UInt64 → Option UInt32) (pc calleeBase : UInt64) (isCall : Bool) : Prop :=
  ∃ w : UInt32,
    code pc = some w ∧
    Arm64.decode w = some (if isCall then .bl (calleeBase - pc) else .b (calleeBase - pc))

/-- Whether instruction index `idx` is covered by a `BRANCH26` or `GOT_LOAD` relocation. -/
def isRelocIdx (branches : List BranchReloc) (gots : List GotReloc) (idx : Nat) : Bool :=
  branches.any (fun b => b.idx == idx) ||
  gots.any (fun g => g.idx == idx || g.idx + 1 == idx)

/-- All unrelocated words of a function match `words`, every `BRANCH26` resolves to
its linked callee, and every `GOT_LOAD` pair resolves (via GOT slot or Apple `ld`
`adrp + add` relaxation) to its linked global address. -/
def FnLoaded (code : UInt64 → Option UInt32) (m : Arm64.Mem) (L : CodeLayout)
    (base : UInt64) (words : Array UInt32)
    (branches : List BranchReloc) (gots : List GotReloc) : Prop :=
  (∀ idx (h : idx < words.size),
    isRelocIdx branches gots idx = false →
    code (base + (4 * idx).toUInt64) = some words[idx]) ∧
  (∀ b ∈ branches,
    BranchAt code (base + (4 * b.idx).toUInt64) (L.symAddr b.target) b.isCall) ∧
  (∀ g ∈ gots,
    Arm64.GotPairAt code m (base + (4 * g.idx).toUInt64) (L.symAddr g.target) g.rd)


/-- Boolean certificate helper checking `Arm64.decode words[k] == some (insn k)` for all `k < n`. -/
def checkWordsAux (words : Array UInt32) (insn : Nat → Arm64.Instr) : Nat → Bool
  | 0 => true
  | k + 1 =>
    (if h : k < words.size then Arm64.decode words[k] == some (insn k) else true) &&
      checkWordsAux words insn k

theorem checkWordsAux_spec (words : Array UInt32) (insn : Nat → Arm64.Instr) :
    ∀ n, checkWordsAux words insn n = true →
      ∀ idx (h : idx < words.size), idx < n → Arm64.decode words[idx] = some (insn idx)
  | 0, _, idx, _, hlt => absurd hlt (Nat.not_lt_zero idx)
  | k + 1, hc, idx, hsz, hlt => by
    simp only [checkWordsAux, Bool.and_eq_true] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact checkWordsAux_spec words insn k hc.2 idx hsz hlt'
    · simp only [hsz, ↓reduceDIte, beq_iff_eq] at hc
      exact hc.1


/-! ### `combine3` (44 instructions) -/

def combine3Words : Array UInt32 := #[
  0xf108001f, 0x54000303, 0x90000008, 0xf9400108, 0xb9400109, 0x90000008, 0xf9400108, 0xb9400108, -- 0..7
  0x2a0903e9, 0x9e670120, 0x0ee0e001, 0x9e660029, 0x9ac95fe9, 0x2a0803ea, 0x9e670141, 0x0ee0e020, -- 8..15
  0x9e66000a, 0x9aca5fea, 0x7200001f, 0x1a8a0108, 0xd341fc0a, 0xf100081f, 0xaa0a03e0, 0x54fffe22, -- 16..23
  0x14000006, 0x90000008, 0xf9400108, 0xf9400108, 0x8b000908, 0xb9401908, 0x2a0103e9, 0x2a0803e8, -- 24..31
  0x9e670120, 0x9e670101, 0x0ee1e000, 0x9e660008, 0x9ac85fe8, 0x4a020108, 0x9e670100, 0x0ee1e000, -- 32..39
  0x9e660008, 0x9ac85fe8, 0x4a030100, 0xd65f03c0 -- 40..43
]

set_option maxRecDepth 8192 in
theorem combine3Words_size : combine3Words.size = 44 := rfl

def combine3Branches : List BranchReloc := []

def combine3Gots : List GotReloc := [
  { idx := 2, rd := ⟨8, by decide⟩, target := .gHwX64 },
  { idx := 5, rd := ⟨8, by decide⟩, target := .gHwOne },
  { idx := 25, rd := ⟨8, by decide⟩, target := .gHwShiftSmallBytes }
]

def combine3Insn (idx : Nat) : Arm64.Instr :=
  if idx < 22 then
    if idx < 11 then
      if idx < 5 then
        if idx < 2 then
          if idx < 1 then
            .addSubImm true true true r31 r0 0x200
          else
            .bCond c3 0x60
        else
          if idx < 3 then
            .adrp r8 0x0
          else
            if idx < 4 then
              .ldrUImm .x64 r8 r8 0x0
            else
              .ldrUImm .w32 r9 r8 0x0
      else
        if idx < 8 then
          if idx < 6 then
            .adrp r8 0x0
          else
            if idx < 7 then
              .ldrUImm .x64 r8 r8 0x0
            else
              .ldrUImm .w32 r8 r8 0x0
        else
          if idx < 9 then
            .logicReg false .orrOp .lsl false r9 r31 r9 0
          else
            if idx < 10 then
              .fmovDX r0 r9
            else
              .pmull1Q r1 r0 r0
    else
      if idx < 16 then
        if idx < 13 then
          if idx < 12 then
            .fmovXD r9 r1
          else
            .crc32c .x64 r9 r31 r9
        else
          if idx < 14 then
            .logicReg false .orrOp .lsl false r10 r31 r8 0
          else
            if idx < 15 then
              .fmovDX r1 r10
            else
              .pmull1Q r0 r1 r0
      else
        if idx < 19 then
          if idx < 17 then
            .fmovXD r10 r0
          else
            if idx < 18 then
              .crc32c .x64 r10 r31 r10
            else
              .logicImm false .andsOp r31 r0 0x1
        else
          if idx < 20 then
            .csel false c0 r8 r8 r10
          else
            if idx < 21 then
              .ubfm true r10 r0 1 63
            else
              .addSubImm true true true r31 r0 0x2
  else
    if idx < 33 then
      if idx < 27 then
        if idx < 24 then
          if idx < 23 then
            .logicReg true .orrOp .lsl false r0 r31 r10 0
          else
            .bCond c2 0xffffffffffffffc4
        else
          if idx < 25 then
            .b 0x18
          else
            if idx < 26 then
              .adrp r8 0x0
            else
              .ldrUImm .x64 r8 r8 0x0
      else
        if idx < 30 then
          if idx < 28 then
            .ldrUImm .x64 r8 r8 0x0
          else
            if idx < 29 then
              .addSubReg true false false .lsl r8 r8 r0 2
            else
              .ldrUImm .w32 r8 r8 0x18
        else
          if idx < 31 then
            .logicReg false .orrOp .lsl false r9 r31 r1 0
          else
            if idx < 32 then
              .logicReg false .orrOp .lsl false r8 r31 r8 0
            else
              .fmovDX r0 r9
    else
      if idx < 38 then
        if idx < 35 then
          if idx < 34 then
            .fmovDX r1 r8
          else
            .pmull1Q r0 r0 r1
        else
          if idx < 36 then
            .fmovXD r8 r0
          else
            if idx < 37 then
              .crc32c .x64 r8 r31 r8
            else
              .logicReg false .eorOp .lsl false r8 r8 r2 0
      else
        if idx < 41 then
          if idx < 39 then
            .fmovDX r0 r8
          else
            if idx < 40 then
              .pmull1Q r0 r0 r1
            else
              .fmovXD r8 r0
        else
          if idx < 42 then
            .crc32c .x64 r8 r31 r8
          else
            if idx < 43 then
              .logicReg false .eorOp .lsl false r0 r8 r3 0
            else
              .ret r30

set_option maxRecDepth 8192 in
private theorem combine3_decode_ok :
    checkWordsAux combine3Words combine3Insn 44 = true := rfl

private theorem combine3_decode_cert (idx : Nat) (hsz : idx < combine3Words.size)
    (hlt : idx < 44) :
    Arm64.decode (combine3Words[idx]'hsz) = some (combine3Insn idx) :=
  checkWordsAux_spec combine3Words combine3Insn 44 combine3_decode_ok idx hsz hlt


/-! ### `combine6` (65 instructions) -/

def combine6Words : Array UInt32 := #[
  0xf108001f, 0x54000303, 0x90000008, 0xf9400108, 0xb9400109, 0x90000008, 0xf9400108, 0xb9400108, -- 0..7
  0x2a0903e9, 0x9e670120, 0x0ee0e001, 0x9e660029, 0x9ac95fe9, 0x2a0803ea, 0x9e670141, 0x0ee0e020, -- 8..15
  0x9e66000a, 0x9aca5fea, 0x7200001f, 0x1a8a0108, 0xd341fc0a, 0xf100081f, 0xaa0a03e0, 0x54fffe22, -- 16..23
  0x14000006, 0x90000008, 0xf9400108, 0xf9400108, 0x8b000908, 0xb9401908, 0x2a0803e8, 0x9e670100, -- 24..31
  0x0ee0e001, 0x9e660028, 0x9ac85fe8, 0x2a0103e9, 0x9e670121, 0x0ee0e021, 0x9e660029, 0x9ac95fe9, -- 32..39
  0x4a020129, 0x2a0303ea, 0x9e670141, 0x0ee0e021, 0x9e66002a, 0x9aca5fea, 0x4a04014a, 0x2a0503eb, -- 40..47
  0x9e670161, 0x0ee0e020, 0x9e66000b, 0x9acb5feb, 0x4a06016b, 0x9e670120, 0x9e670101, 0x0ee1e000, -- 48..55
  0x9e660008, 0x9ac85fe8, 0x4a080148, 0x9e670100, 0x0ee1e000, 0x9e660008, 0x9ac85fe8, 0x4a080160, -- 56..63
  0xd65f03c0 -- 64..64
]

set_option maxRecDepth 8192 in
theorem combine6Words_size : combine6Words.size = 65 := rfl

def combine6Branches : List BranchReloc := []

def combine6Gots : List GotReloc := [
  { idx := 2, rd := ⟨8, by decide⟩, target := .gHwX64 },
  { idx := 5, rd := ⟨8, by decide⟩, target := .gHwOne },
  { idx := 25, rd := ⟨8, by decide⟩, target := .gHwShiftSmallBytes }
]

def combine6Insn (idx : Nat) : Arm64.Instr :=
  if idx < 32 then
    if idx < 16 then
      if idx < 8 then
        if idx < 4 then
          if idx < 2 then
            if idx < 1 then
              .addSubImm true true true r31 r0 0x200
            else
              .bCond c3 0x60
          else
            if idx < 3 then
              .adrp r8 0x0
            else
              .ldrUImm .x64 r8 r8 0x0
        else
          if idx < 6 then
            if idx < 5 then
              .ldrUImm .w32 r9 r8 0x0
            else
              .adrp r8 0x0
          else
            if idx < 7 then
              .ldrUImm .x64 r8 r8 0x0
            else
              .ldrUImm .w32 r8 r8 0x0
      else
        if idx < 12 then
          if idx < 10 then
            if idx < 9 then
              .logicReg false .orrOp .lsl false r9 r31 r9 0
            else
              .fmovDX r0 r9
          else
            if idx < 11 then
              .pmull1Q r1 r0 r0
            else
              .fmovXD r9 r1
        else
          if idx < 14 then
            if idx < 13 then
              .crc32c .x64 r9 r31 r9
            else
              .logicReg false .orrOp .lsl false r10 r31 r8 0
          else
            if idx < 15 then
              .fmovDX r1 r10
            else
              .pmull1Q r0 r1 r0
    else
      if idx < 24 then
        if idx < 20 then
          if idx < 18 then
            if idx < 17 then
              .fmovXD r10 r0
            else
              .crc32c .x64 r10 r31 r10
          else
            if idx < 19 then
              .logicImm false .andsOp r31 r0 0x1
            else
              .csel false c0 r8 r8 r10
        else
          if idx < 22 then
            if idx < 21 then
              .ubfm true r10 r0 1 63
            else
              .addSubImm true true true r31 r0 0x2
          else
            if idx < 23 then
              .logicReg true .orrOp .lsl false r0 r31 r10 0
            else
              .bCond c2 0xffffffffffffffc4
      else
        if idx < 28 then
          if idx < 26 then
            if idx < 25 then
              .b 0x18
            else
              .adrp r8 0x0
          else
            if idx < 27 then
              .ldrUImm .x64 r8 r8 0x0
            else
              .ldrUImm .x64 r8 r8 0x0
        else
          if idx < 30 then
            if idx < 29 then
              .addSubReg true false false .lsl r8 r8 r0 2
            else
              .ldrUImm .w32 r8 r8 0x18
          else
            if idx < 31 then
              .logicReg false .orrOp .lsl false r8 r31 r8 0
            else
              .fmovDX r0 r8
  else
    if idx < 48 then
      if idx < 40 then
        if idx < 36 then
          if idx < 34 then
            if idx < 33 then
              .pmull1Q r1 r0 r0
            else
              .fmovXD r8 r1
          else
            if idx < 35 then
              .crc32c .x64 r8 r31 r8
            else
              .logicReg false .orrOp .lsl false r9 r31 r1 0
        else
          if idx < 38 then
            if idx < 37 then
              .fmovDX r1 r9
            else
              .pmull1Q r1 r1 r0
          else
            if idx < 39 then
              .fmovXD r9 r1
            else
              .crc32c .x64 r9 r31 r9
      else
        if idx < 44 then
          if idx < 42 then
            if idx < 41 then
              .logicReg false .eorOp .lsl false r9 r9 r2 0
            else
              .logicReg false .orrOp .lsl false r10 r31 r3 0
          else
            if idx < 43 then
              .fmovDX r1 r10
            else
              .pmull1Q r1 r1 r0
        else
          if idx < 46 then
            if idx < 45 then
              .fmovXD r10 r1
            else
              .crc32c .x64 r10 r31 r10
          else
            if idx < 47 then
              .logicReg false .eorOp .lsl false r10 r10 r4 0
            else
              .logicReg false .orrOp .lsl false r11 r31 r5 0
    else
      if idx < 56 then
        if idx < 52 then
          if idx < 50 then
            if idx < 49 then
              .fmovDX r1 r11
            else
              .pmull1Q r0 r1 r0
          else
            if idx < 51 then
              .fmovXD r11 r0
            else
              .crc32c .x64 r11 r31 r11
        else
          if idx < 54 then
            if idx < 53 then
              .logicReg false .eorOp .lsl false r11 r11 r6 0
            else
              .fmovDX r0 r9
          else
            if idx < 55 then
              .fmovDX r1 r8
            else
              .pmull1Q r0 r0 r1
      else
        if idx < 60 then
          if idx < 58 then
            if idx < 57 then
              .fmovXD r8 r0
            else
              .crc32c .x64 r8 r31 r8
          else
            if idx < 59 then
              .logicReg false .eorOp .lsl false r8 r10 r8 0
            else
              .fmovDX r0 r8
        else
          if idx < 62 then
            if idx < 61 then
              .pmull1Q r0 r0 r1
            else
              .fmovXD r8 r0
          else
            if idx < 63 then
              .crc32c .x64 r8 r31 r8
            else
              if idx < 64 then
                .logicReg false .eorOp .lsl false r0 r11 r8 0
              else
                .ret r30

set_option maxRecDepth 8192 in
private theorem combine6_decode_ok :
    checkWordsAux combine6Words combine6Insn 65 = true := rfl

private theorem combine6_decode_cert (idx : Nat) (hsz : idx < combine6Words.size)
    (hlt : idx < 65) :
    Arm64.decode (combine6Words[idx]'hsz) = some (combine6Insn idx) :=
  checkWordsAux_spec combine6Words combine6Insn 65 combine6_decode_ok idx hsz hlt


/-! ### `hwLoop` (99 instructions) -/

def hwLoopWords : Array UInt32 := #[
  0xcb010048, 0xf100411f, 0x54000163, 0x8b000029, 0x91008129, 0x91004021, 0xa97fad2a, 0x9aca5c6a, -- 0..7
  0x9acb5d43, 0x91004129, 0xd1004108, 0xf100411f, 0x54ffff22, 0xf1001d1f, 0x54000148, 0xf1000d1f, -- 8..15
  0x540002a8, 0xf100051f, 0x540005c8, 0xeb02003f, 0x540009a2, 0x8b010008, 0x91006108, 0x14000047, -- 16..23
  0x9100202a, 0x91006008, 0x8b010109, 0xf940012b, 0x9acb5c63, 0xcb0a004b, 0xf1000d7f, 0x54000248, -- 24..31
  0xf100057f, 0x540004e8, 0xeb0a005f, 0x54000748, 0x1400003d, 0x91001029, 0x91006008, 0x8b01010a, -- 32..39
  0xb940014b, 0x1acb5863, 0xcb09004b, 0xf100057f, 0x54000428, 0xeb09005f, 0x54000669, 0x8b090108, -- 40..47
  0x1400002e, 0x9100302b, 0x386a690a, 0x3940252c, 0x3940292d, 0x2a0c214a, 0x2a0d414a, 0x39402d2c, -- 48..55
  0x2a0c614a, 0x1aca5863, 0xcb0b004a, 0xf100055f, 0x54000348, 0xeb0b005f, 0x54000469, 0x14000015, -- 56..63
  0x91000828, 0x91006009, 0x7861692a, 0x1aca5463, 0xeb02011f, 0x54000382, 0x8b080128, 0x14000017, -- 64..71
  0x9100282b, 0x386a690a, 0x39402529, 0x2a092149, 0x14000005, 0x9100182b, 0x38696909, 0x3940154a, -- 72..79
  0x2a0a2129, 0x1ac95463, 0xeb02017f, 0x540001c2, 0x8b0b0108, 0x14000009, 0x9100382a, 0x386b690b, -- 80..87
  0x39403529, 0x2a092169, 0x1ac95463, 0xeb02015f, 0x540000a2, 0x8b0a0108, 0x39400108, 0x1ac85060, -- 88..95
  0xd65f03c0, 0xaa0303e0, 0xd65f03c0 -- 96..98
]

set_option maxRecDepth 8192 in
theorem hwLoopWords_size : hwLoopWords.size = 99 := rfl

def hwLoopBranches : List BranchReloc := []

def hwLoopGots : List GotReloc := []

def hwLoopInsn (idx : Nat) : Arm64.Instr :=
  if idx < 49 then
    if idx < 24 then
      if idx < 12 then
        if idx < 6 then
          if idx < 3 then
            if idx < 1 then
              .addSubReg true true false .lsl r8 r2 r1 0
            else
              if idx < 2 then
                .addSubImm true true true r31 r8 0x10
              else
                .bCond c3 0x2c
          else
            if idx < 4 then
              .addSubReg true false false .lsl r9 r1 r0 0
            else
              if idx < 5 then
                .addSubImm true false false r9 r9 0x20
              else
                .addSubImm true false false r1 r1 0x10
        else
          if idx < 9 then
            if idx < 7 then
              .ldpGP true .signedOffset r10 r11 r9 0xfffffffffffffff8
            else
              if idx < 8 then
                .crc32c .x64 r10 r3 r10
              else
                .crc32c .x64 r3 r10 r11
          else
            if idx < 10 then
              .addSubImm true false false r9 r9 0x10
            else
              if idx < 11 then
                .addSubImm true true false r8 r8 0x10
              else
                .addSubImm true true true r31 r8 0x10
      else
        if idx < 18 then
          if idx < 15 then
            if idx < 13 then
              .bCond c2 0xffffffffffffffe4
            else
              if idx < 14 then
                .addSubImm true true true r31 r8 0x7
              else
                .bCond c8 0x28
          else
            if idx < 16 then
              .addSubImm true true true r31 r8 0x3
            else
              if idx < 17 then
                .bCond c8 0x54
              else
                .addSubImm true true true r31 r8 0x1
        else
          if idx < 21 then
            if idx < 19 then
              .bCond c8 0xb8
            else
              if idx < 20 then
                .addSubReg true true true .lsl r31 r1 r2 0
              else
                .bCond c2 0x134
          else
            if idx < 22 then
              .addSubReg true false false .lsl r8 r0 r1 0
            else
              if idx < 23 then
                .addSubImm true false false r8 r8 0x18
              else
                .b 0x11c
    else
      if idx < 36 then
        if idx < 30 then
          if idx < 27 then
            if idx < 25 then
              .addSubImm true false false r10 r1 0x8
            else
              if idx < 26 then
                .addSubImm true false false r8 r0 0x18
              else
                .addSubReg true false false .lsl r9 r8 r1 0
          else
            if idx < 28 then
              .ldrUImm .x64 r11 r9 0x0
            else
              if idx < 29 then
                .crc32c .x64 r3 r3 r11
              else
                .addSubReg true true false .lsl r11 r2 r10 0
        else
          if idx < 33 then
            if idx < 31 then
              .addSubImm true true true r31 r11 0x3
            else
              if idx < 32 then
                .bCond c8 0x48
              else
                .addSubImm true true true r31 r11 0x1
          else
            if idx < 34 then
              .bCond c8 0x9c
            else
              if idx < 35 then
                .addSubReg true true true .lsl r31 r2 r10 0
              else
                .bCond c8 0xe8
      else
        if idx < 42 then
          if idx < 39 then
            if idx < 37 then
              .b 0xf4
            else
              if idx < 38 then
                .addSubImm true false false r9 r1 0x4
              else
                .addSubImm true false false r8 r0 0x18
          else
            if idx < 40 then
              .addSubReg true false false .lsl r10 r8 r1 0
            else
              if idx < 41 then
                .ldrUImm .w32 r11 r10 0x0
              else
                .crc32c .w32 r3 r3 r11
        else
          if idx < 45 then
            if idx < 43 then
              .addSubReg true true false .lsl r11 r2 r9 0
            else
              if idx < 44 then
                .addSubImm true true true r31 r11 0x1
              else
                .bCond c8 0x84
          else
            if idx < 47 then
              if idx < 46 then
                .addSubReg true true true .lsl r31 r2 r9 0
              else
                .bCond c9 0xcc
            else
              if idx < 48 then
                .addSubReg true false false .lsl r8 r8 r9 0
              else
                .b 0xb8
  else
    if idx < 74 then
      if idx < 61 then
        if idx < 55 then
          if idx < 52 then
            if idx < 50 then
              .addSubImm true false false r11 r1 0xc
            else
              if idx < 51 then
                .ldrReg .b8 r10 r8 r10
              else
                .ldrUImm .b8 r12 r9 0x9
          else
            if idx < 53 then
              .ldrUImm .b8 r13 r9 0xa
            else
              if idx < 54 then
                .logicReg false .orrOp .lsl false r10 r10 r12 8
              else
                .logicReg false .orrOp .lsl false r10 r10 r13 16
        else
          if idx < 58 then
            if idx < 56 then
              .ldrUImm .b8 r12 r9 0xb
            else
              if idx < 57 then
                .logicReg false .orrOp .lsl false r10 r10 r12 24
              else
                .crc32c .w32 r3 r3 r10
          else
            if idx < 59 then
              .addSubReg true true false .lsl r10 r2 r11 0
            else
              if idx < 60 then
                .addSubImm true true true r31 r10 0x1
              else
                .bCond c8 0x68
      else
        if idx < 67 then
          if idx < 64 then
            if idx < 62 then
              .addSubReg true true true .lsl r31 r2 r11 0
            else
              if idx < 63 then
                .bCond c9 0x8c
              else
                .b 0x54
          else
            if idx < 65 then
              .addSubImm true false false r8 r1 0x2
            else
              if idx < 66 then
                .addSubImm true false false r9 r0 0x18
              else
                .ldrReg .h16 r10 r9 r1
        else
          if idx < 70 then
            if idx < 68 then
              .crc32c .h16 r3 r3 r10
            else
              if idx < 69 then
                .addSubReg true true true .lsl r31 r8 r2 0
              else
                .bCond c2 0x70
          else
            if idx < 72 then
              if idx < 71 then
                .addSubReg true false false .lsl r8 r9 r8 0
              else
                .b 0x5c
            else
              if idx < 73 then
                .addSubImm true false false r11 r1 0xa
              else
                .ldrReg .b8 r10 r8 r10
    else
      if idx < 86 then
        if idx < 80 then
          if idx < 77 then
            if idx < 75 then
              .ldrUImm .b8 r9 r9 0x9
            else
              if idx < 76 then
                .logicReg false .orrOp .lsl false r9 r10 r9 8
              else
                .b 0x14
          else
            if idx < 78 then
              .addSubImm true false false r11 r1 0x6
            else
              if idx < 79 then
                .ldrReg .b8 r9 r8 r9
              else
                .ldrUImm .b8 r10 r10 0x5
        else
          if idx < 83 then
            if idx < 81 then
              .logicReg false .orrOp .lsl false r9 r9 r10 8
            else
              if idx < 82 then
                .crc32c .h16 r3 r3 r9
              else
                .addSubReg true true true .lsl r31 r11 r2 0
          else
            if idx < 84 then
              .bCond c2 0x38
            else
              if idx < 85 then
                .addSubReg true false false .lsl r8 r8 r11 0
              else
                .b 0x24
      else
        if idx < 92 then
          if idx < 89 then
            if idx < 87 then
              .addSubImm true false false r10 r1 0xe
            else
              if idx < 88 then
                .ldrReg .b8 r11 r8 r11
              else
                .ldrUImm .b8 r9 r9 0xd
          else
            if idx < 90 then
              .logicReg false .orrOp .lsl false r9 r11 r9 8
            else
              if idx < 91 then
                .crc32c .h16 r3 r3 r9
              else
                .addSubReg true true true .lsl r31 r10 r2 0
        else
          if idx < 95 then
            if idx < 93 then
              .bCond c2 0x14
            else
              if idx < 94 then
                .addSubReg true false false .lsl r8 r8 r10 0
              else
                .ldrUImm .b8 r8 r8 0x0
          else
            if idx < 97 then
              if idx < 96 then
                .crc32c .b8 r0 r3 r8
              else
                .ret r30
            else
              if idx < 98 then
                .logicReg true .orrOp .lsl false r0 r31 r3 0
              else
                .ret r30

set_option maxRecDepth 8192 in
private theorem hwLoop_decode_ok :
    checkWordsAux hwLoopWords hwLoopInsn 99 = true := rfl

private theorem hwLoop_decode_cert (idx : Nat) (hsz : idx < hwLoopWords.size)
    (hlt : idx < 99) :
    Arm64.decode (hwLoopWords[idx]'hsz) = some (hwLoopInsn idx) :=
  checkWordsAux_spec hwLoopWords hwLoopInsn 99 hwLoop_decode_ok idx hsz hlt


/-! ### `hwFold6Loop` (197 instructions) -/

def hwFold6LoopWords : Array UInt32 := #[
  0x6dba23e9, 0xa9016ffc, 0xa90267fa, 0xa9035ff8, 0xa90457f6, 0xa9054ff4, 0xaa0303ea, 0xaa0203e8, -- 0..7
  0xaa0103e9, 0xa949afec, 0xa948bbef, 0xa947d3f3, 0x294d8fe2, 0xb9406be1, 0xeb08013f, 0x54001402, -- 8..15
  0xf94033f0, 0x90000011, 0xf9400231, 0x9100600d, 0xf9400235, 0x90000011, 0xf9400231, 0x90000000, -- 16..23
  0xf9400000, 0xf9400236, 0xf9400017, 0x90000011, 0xf9400231, 0x90000000, 0xf9400000, 0xf9400238, -- 24..31
  0xf9400019, 0x90000011, 0xf9400231, 0x90000000, 0xf9400000, 0xf940023a, 0xf940001b, 0x9000001c, -- 32..39
  0xf940039c, 0x8b1001b0, 0x8b0701b1, 0x8b0601a0, 0x8b0501a5, 0x8b0401a4, 0x9e6702a0, 0x9e6702c1, -- 40..47
  0x9e6702e2, 0x9e670303, 0xf9400386, 0x9e670324, 0x9e670345, 0x9e670366, 0x9e6700c7, 0x8b0901a6, -- 48..55
  0xa94054c7, 0x9ac75c21, 0x9ad55c21, 0xa94154c7, 0x9ac75c21, 0x9ad55c21, 0xa94254c7, 0x9ac75c21, -- 56..63
  0x9ad55c21, 0xa94318c7, 0x9ac75c21, 0x9ac65c21, 0x8b090086, 0xa94054c7, 0x9ac75c42, 0x9ad55c42, -- 64..71
  0xa94154c7, 0x9ac75c42, 0x9ad55c42, 0xa94254c7, 0x9ac75c42, 0x9ad55c42, 0xa94318c7, 0x9ac75c42, -- 72..79
  0x9ac65c42, 0x8b0900a6, 0xa94054c7, 0x9ac75c63, 0x9ad55c63, 0xa94154c7, 0x9ac75c63, 0x9ad55c76, -- 80..87
  0xa94260d7, 0xa9430cd5, 0x8b090006, 0x9e670270, 0x9e670291, 0xa94350d3, 0x0ee0e212, 0x0ee1e233, -- 88..95
  0x6d4050d0, 0x0ee2e215, 0x6d415cd6, 0x6d4264d8, 0x8b090227, 0x3dc00cf1, 0x9ad75ed6, 0x8b090206, -- 96..103
  0x3dc00cd0, 0x0ee3e294, 0x0ee4e2d6, 0x0ee5e2f7, 0x0ee6e318, 0x0ee7e339, 0x9ad85ed6, 0x4ed87b3a, -- 104..111
  0x6e180719, 0x4ed67af8, 0x9ad55ed5, 0x6e1806d7, 0x4ed57a96, 0x9ac35ea3, 0x6e1806b4, 0x4ed27a75, -- 112..119
  0x6e180653, 0x91010129, 0x6e331ef2, 0xce144b32, 0x6e124253, 0x2e331e52, 0x9e660255, 0xca1302b3, -- 120..127
  0x6e351f12, 0xce164b52, 0x6e124253, 0x2e331e52, 0x9e660255, 0xca1402b4, 0x9e6701f2, 0x0ee0e252, -- 128..135
  0x9e6701d3, 0x0ee1e273, 0x6d4054f4, 0x0ee2e294, 0x0ee3e2b5, 0x6d415cf6, 0x0ee4e2d6, 0x0ee5e2f7, -- 136..143
  0x6d4264f8, 0x0ee6e318, 0x0ee7e339, 0x9e67019a, 0x0ee0e35a, 0x9e67017b, 0x0ee1e37b, 0x6d4074dc, -- 144..151
  0x0ee2e39c, 0x0ee3e3bd, 0x6d417cde, 0x0ee4e3de, 0x0ee5e3ff, 0x6d4224c8, 0x0ee6e108, 0x0ee7e129, -- 152..159
  0xce124e31, 0xce145631, 0xce165e31, 0xce186631, 0xce1a6e10, 0xce1c7610, 0xce1e7e10, 0xce082610, -- 160..167
  0x9e66020c, 0x4e183e0b, 0x9e66022f, 0x4e183e2e, 0xeb08013f, 0x54fff143, 0x14000005, 0x9e6701f1, -- 168..175
  0x4e181dd1, 0x9e670190, 0x4e181d70, 0x9ad35fe8, 0x9ad45d04, 0x9e660228, 0x9ac85fe8, 0x4e183e29, -- 176..183
  0x9ac95d05, 0x9e660208, 0x9ac85fe8, 0x4e183e09, 0x9ac95d06, 0xaa0a03e0, 0xa9454ff4, 0xa94457f6, -- 184..191
  0xa9435ff8, 0xa94267fa, 0xa9416ffc, 0x6cc623e9, 0x14000000 -- 192..196
]

set_option maxRecDepth 8192 in
theorem hwFold6LoopWords_size : hwFold6LoopWords.size = 197 := rfl

def hwFold6LoopBranches : List BranchReloc := [
  { idx := 196, isCall := false, target := .fnCombine6 }
]

def hwFold6LoopGots : List GotReloc := [
  { idx := 17, rd := ⟨17, by decide⟩, target := .gKFold512_1 },
  { idx := 21, rd := ⟨17, by decide⟩, target := .gKFold512_2 },
  { idx := 23, rd := ⟨0, by decide⟩, target := .gKFold384_1 },
  { idx := 27, rd := ⟨17, by decide⟩, target := .gKFold384_2 },
  { idx := 29, rd := ⟨0, by decide⟩, target := .gKFold256_1 },
  { idx := 33, rd := ⟨17, by decide⟩, target := .gKFold256_2 },
  { idx := 35, rd := ⟨0, by decide⟩, target := .gKFold128_1 },
  { idx := 39, rd := ⟨28, by decide⟩, target := .gKFold128_2 }
]

def hwFold6LoopInsn (idx : Nat) : Arm64.Instr :=
  if idx < 98 then
    if idx < 49 then
      if idx < 24 then
        if idx < 12 then
          if idx < 6 then
            if idx < 3 then
              if idx < 1 then
                .stpD .preIndex r9 r8 r31 0xffffffffffffffa0
              else
                if idx < 2 then
                  .stpGP true .signedOffset r28 r27 r31 0x10
                else
                  .stpGP true .signedOffset r26 r25 r31 0x20
            else
              if idx < 4 then
                .stpGP true .signedOffset r24 r23 r31 0x30
              else
                if idx < 5 then
                  .stpGP true .signedOffset r22 r21 r31 0x40
                else
                  .stpGP true .signedOffset r20 r19 r31 0x50
          else
            if idx < 9 then
              if idx < 7 then
                .logicReg true .orrOp .lsl false r10 r31 r3 0
              else
                if idx < 8 then
                  .logicReg true .orrOp .lsl false r8 r31 r2 0
                else
                  .logicReg true .orrOp .lsl false r9 r31 r1 0
            else
              if idx < 10 then
                .ldpGP true .signedOffset r12 r11 r31 0x98
              else
                if idx < 11 then
                  .ldpGP true .signedOffset r15 r14 r31 0x88
                else
                  .ldpGP true .signedOffset r19 r20 r31 0x78
        else
          if idx < 18 then
            if idx < 15 then
              if idx < 13 then
                .ldpGP false .signedOffset r2 r3 r31 0x6c
              else
                if idx < 14 then
                  .ldrUImm .w32 r1 r31 0x68
                else
                  .addSubReg true true true .lsl r31 r9 r8 0
            else
              if idx < 16 then
                .bCond c2 0x280
              else
                if idx < 17 then
                  .ldrUImm .x64 r16 r31 0x60
                else
                  .adrp r17 0x0
          else
            if idx < 21 then
              if idx < 19 then
                .ldrUImm .x64 r17 r17 0x0
              else
                if idx < 20 then
                  .addSubImm true false false r13 r0 0x18
                else
                  .ldrUImm .x64 r21 r17 0x0
            else
              if idx < 22 then
                .adrp r17 0x0
              else
                if idx < 23 then
                  .ldrUImm .x64 r17 r17 0x0
                else
                  .adrp r0 0x0
      else
        if idx < 36 then
          if idx < 30 then
            if idx < 27 then
              if idx < 25 then
                .ldrUImm .x64 r0 r0 0x0
              else
                if idx < 26 then
                  .ldrUImm .x64 r22 r17 0x0
                else
                  .ldrUImm .x64 r23 r0 0x0
            else
              if idx < 28 then
                .adrp r17 0x0
              else
                if idx < 29 then
                  .ldrUImm .x64 r17 r17 0x0
                else
                  .adrp r0 0x0
          else
            if idx < 33 then
              if idx < 31 then
                .ldrUImm .x64 r0 r0 0x0
              else
                if idx < 32 then
                  .ldrUImm .x64 r24 r17 0x0
                else
                  .ldrUImm .x64 r25 r0 0x0
            else
              if idx < 34 then
                .adrp r17 0x0
              else
                if idx < 35 then
                  .ldrUImm .x64 r17 r17 0x0
                else
                  .adrp r0 0x0
        else
          if idx < 42 then
            if idx < 39 then
              if idx < 37 then
                .ldrUImm .x64 r0 r0 0x0
              else
                if idx < 38 then
                  .ldrUImm .x64 r26 r17 0x0
                else
                  .ldrUImm .x64 r27 r0 0x0
            else
              if idx < 40 then
                .adrp r28 0x0
              else
                if idx < 41 then
                  .ldrUImm .x64 r28 r28 0x0
                else
                  .addSubReg true false false .lsl r16 r13 r16 0
          else
            if idx < 45 then
              if idx < 43 then
                .addSubReg true false false .lsl r17 r13 r7 0
              else
                if idx < 44 then
                  .addSubReg true false false .lsl r0 r13 r6 0
                else
                  .addSubReg true false false .lsl r5 r13 r5 0
            else
              if idx < 47 then
                if idx < 46 then
                  .addSubReg true false false .lsl r4 r13 r4 0
                else
                  .fmovDX r0 r21
              else
                if idx < 48 then
                  .fmovDX r1 r22
                else
                  .fmovDX r2 r23
    else
      if idx < 73 then
        if idx < 61 then
          if idx < 55 then
            if idx < 52 then
              if idx < 50 then
                .fmovDX r3 r24
              else
                if idx < 51 then
                  .ldrUImm .x64 r6 r28 0x0
                else
                  .fmovDX r4 r25
            else
              if idx < 53 then
                .fmovDX r5 r26
              else
                if idx < 54 then
                  .fmovDX r6 r27
                else
                  .fmovDX r7 r6
          else
            if idx < 58 then
              if idx < 56 then
                .addSubReg true false false .lsl r6 r13 r9 0
              else
                if idx < 57 then
                  .ldpGP true .signedOffset r7 r21 r6 0x0
                else
                  .crc32c .x64 r1 r1 r7
            else
              if idx < 59 then
                .crc32c .x64 r1 r1 r21
              else
                if idx < 60 then
                  .ldpGP true .signedOffset r7 r21 r6 0x10
                else
                  .crc32c .x64 r1 r1 r7
        else
          if idx < 67 then
            if idx < 64 then
              if idx < 62 then
                .crc32c .x64 r1 r1 r21
              else
                if idx < 63 then
                  .ldpGP true .signedOffset r7 r21 r6 0x20
                else
                  .crc32c .x64 r1 r1 r7
            else
              if idx < 65 then
                .crc32c .x64 r1 r1 r21
              else
                if idx < 66 then
                  .ldpGP true .signedOffset r7 r6 r6 0x30
                else
                  .crc32c .x64 r1 r1 r7
          else
            if idx < 70 then
              if idx < 68 then
                .crc32c .x64 r1 r1 r6
              else
                if idx < 69 then
                  .addSubReg true false false .lsl r6 r4 r9 0
                else
                  .ldpGP true .signedOffset r7 r21 r6 0x0
            else
              if idx < 71 then
                .crc32c .x64 r2 r2 r7
              else
                if idx < 72 then
                  .crc32c .x64 r2 r2 r21
                else
                  .ldpGP true .signedOffset r7 r21 r6 0x10
      else
        if idx < 85 then
          if idx < 79 then
            if idx < 76 then
              if idx < 74 then
                .crc32c .x64 r2 r2 r7
              else
                if idx < 75 then
                  .crc32c .x64 r2 r2 r21
                else
                  .ldpGP true .signedOffset r7 r21 r6 0x20
            else
              if idx < 77 then
                .crc32c .x64 r2 r2 r7
              else
                if idx < 78 then
                  .crc32c .x64 r2 r2 r21
                else
                  .ldpGP true .signedOffset r7 r6 r6 0x30
          else
            if idx < 82 then
              if idx < 80 then
                .crc32c .x64 r2 r2 r7
              else
                if idx < 81 then
                  .crc32c .x64 r2 r2 r6
                else
                  .addSubReg true false false .lsl r6 r5 r9 0
            else
              if idx < 83 then
                .ldpGP true .signedOffset r7 r21 r6 0x0
              else
                if idx < 84 then
                  .crc32c .x64 r3 r3 r7
                else
                  .crc32c .x64 r3 r3 r21
        else
          if idx < 91 then
            if idx < 88 then
              if idx < 86 then
                .ldpGP true .signedOffset r7 r21 r6 0x10
              else
                if idx < 87 then
                  .crc32c .x64 r3 r3 r7
                else
                  .crc32c .x64 r22 r3 r21
            else
              if idx < 89 then
                .ldpGP true .signedOffset r23 r24 r6 0x20
              else
                if idx < 90 then
                  .ldpGP true .signedOffset r21 r3 r6 0x30
                else
                  .addSubReg true false false .lsl r6 r0 r9 0
          else
            if idx < 94 then
              if idx < 92 then
                .fmovDX r16 r19
              else
                if idx < 93 then
                  .fmovDX r17 r20
                else
                  .ldpGP true .signedOffset r19 r20 r6 0x30
            else
              if idx < 96 then
                if idx < 95 then
                  .pmull1Q r18 r16 r0
                else
                  .pmull1Q r19 r17 r1
              else
                if idx < 97 then
                  .ldpD .signedOffset r16 r20 r6 0x0
                else
                  .pmull1Q r21 r16 r2
  else
    if idx < 147 then
      if idx < 122 then
        if idx < 110 then
          if idx < 104 then
            if idx < 101 then
              if idx < 99 then
                .ldpD .signedOffset r22 r23 r6 0x10
              else
                if idx < 100 then
                  .ldpD .signedOffset r24 r25 r6 0x20
                else
                  .addSubReg true false false .lsl r7 r17 r9 0
            else
              if idx < 102 then
                .ldrQImm r17 r7 0x30
              else
                if idx < 103 then
                  .crc32c .x64 r22 r22 r23
                else
                  .addSubReg true false false .lsl r6 r16 r9 0
          else
            if idx < 107 then
              if idx < 105 then
                .ldrQImm r16 r6 0x30
              else
                if idx < 106 then
                  .pmull1Q r20 r20 r3
                else
                  .pmull1Q r22 r22 r4
            else
              if idx < 108 then
                .pmull1Q r23 r23 r5
              else
                if idx < 109 then
                  .pmull1Q r24 r24 r6
                else
                  .pmull1Q r25 r25 r7
        else
          if idx < 116 then
            if idx < 113 then
              if idx < 111 then
                .crc32c .x64 r22 r22 r24
              else
                if idx < 112 then
                  .zip2_2D r26 r25 r24
                else
                  .insDV r25 l1 r24 l0
            else
              if idx < 114 then
                .zip2_2D r24 r23 r22
              else
                if idx < 115 then
                  .crc32c .x64 r21 r22 r21
                else
                  .insDV r23 l1 r22 l0
          else
            if idx < 119 then
              if idx < 117 then
                .zip2_2D r22 r20 r21
              else
                if idx < 118 then
                  .crc32c .x64 r3 r21 r3
                else
                  .insDV r20 l1 r21 l0
            else
              if idx < 120 then
                .zip2_2D r21 r19 r18
              else
                if idx < 121 then
                  .insDV r19 l1 r18 l0
                else
                  .addSubImm true false false r9 r9 0x40
      else
        if idx < 134 then
          if idx < 128 then
            if idx < 125 then
              if idx < 123 then
                .eorVec true r18 r23 r19
              else
                if idx < 124 then
                  .eor3_16B r18 r25 r20 r18
                else
                  .ext16B r19 r18 r18 c8
            else
              if idx < 126 then
                .eorVec false r18 r18 r19
              else
                if idx < 127 then
                  .fmovXD r21 r18
                else
                  .logicReg true .eorOp .lsl false r19 r21 r19 0
          else
            if idx < 131 then
              if idx < 129 then
                .eorVec true r18 r24 r21
              else
                if idx < 130 then
                  .eor3_16B r18 r26 r22 r18
                else
                  .ext16B r19 r18 r18 c8
            else
              if idx < 132 then
                .eorVec false r18 r18 r19
              else
                if idx < 133 then
                  .fmovXD r21 r18
                else
                  .logicReg true .eorOp .lsl false r20 r21 r20 0
        else
          if idx < 140 then
            if idx < 137 then
              if idx < 135 then
                .fmovDX r18 r15
              else
                if idx < 136 then
                  .pmull1Q r18 r18 r0
                else
                  .fmovDX r19 r14
            else
              if idx < 138 then
                .pmull1Q r19 r19 r1
              else
                if idx < 139 then
                  .ldpD .signedOffset r20 r21 r7 0x0
                else
                  .pmull1Q r20 r20 r2
          else
            if idx < 143 then
              if idx < 141 then
                .pmull1Q r21 r21 r3
              else
                if idx < 142 then
                  .ldpD .signedOffset r22 r23 r7 0x10
                else
                  .pmull1Q r22 r22 r4
            else
              if idx < 145 then
                if idx < 144 then
                  .pmull1Q r23 r23 r5
                else
                  .ldpD .signedOffset r24 r25 r7 0x20
              else
                if idx < 146 then
                  .pmull1Q r24 r24 r6
                else
                  .pmull1Q r25 r25 r7
    else
      if idx < 172 then
        if idx < 159 then
          if idx < 153 then
            if idx < 150 then
              if idx < 148 then
                .fmovDX r26 r12
              else
                if idx < 149 then
                  .pmull1Q r26 r26 r0
                else
                  .fmovDX r27 r11
            else
              if idx < 151 then
                .pmull1Q r27 r27 r1
              else
                if idx < 152 then
                  .ldpD .signedOffset r28 r29 r6 0x0
                else
                  .pmull1Q r28 r28 r2
          else
            if idx < 156 then
              if idx < 154 then
                .pmull1Q r29 r29 r3
              else
                if idx < 155 then
                  .ldpD .signedOffset r30 r31 r6 0x10
                else
                  .pmull1Q r30 r30 r4
            else
              if idx < 157 then
                .pmull1Q r31 r31 r5
              else
                if idx < 158 then
                  .ldpD .signedOffset r8 r9 r6 0x20
                else
                  .pmull1Q r8 r8 r6
        else
          if idx < 165 then
            if idx < 162 then
              if idx < 160 then
                .pmull1Q r9 r9 r7
              else
                if idx < 161 then
                  .eor3_16B r17 r17 r18 r19
                else
                  .eor3_16B r17 r17 r20 r21
            else
              if idx < 163 then
                .eor3_16B r17 r17 r22 r23
              else
                if idx < 164 then
                  .eor3_16B r17 r17 r24 r25
                else
                  .eor3_16B r16 r16 r26 r27
          else
            if idx < 168 then
              if idx < 166 then
                .eor3_16B r16 r16 r28 r29
              else
                if idx < 167 then
                  .eor3_16B r16 r16 r30 r31
                else
                  .eor3_16B r16 r16 r8 r9
            else
              if idx < 170 then
                if idx < 169 then
                  .fmovXD r12 r16
                else
                  .umovD r11 r16 l1
              else
                if idx < 171 then
                  .fmovXD r15 r17
                else
                  .umovD r14 r17 l1
      else
        if idx < 184 then
          if idx < 178 then
            if idx < 175 then
              if idx < 173 then
                .addSubReg true true true .lsl r31 r9 r8 0
              else
                if idx < 174 then
                  .bCond c3 0xfffffffffffffe28
                else
                  .b 0x14
            else
              if idx < 176 then
                .fmovDX r17 r15
              else
                if idx < 177 then
                  .insDX r17 l1 r14
                else
                  .fmovDX r16 r12
          else
            if idx < 181 then
              if idx < 179 then
                .insDX r16 l1 r11
              else
                if idx < 180 then
                  .crc32c .x64 r8 r31 r19
                else
                  .crc32c .x64 r4 r8 r20
            else
              if idx < 182 then
                .fmovXD r8 r17
              else
                if idx < 183 then
                  .crc32c .x64 r8 r31 r8
                else
                  .umovD r9 r17 l1
        else
          if idx < 190 then
            if idx < 187 then
              if idx < 185 then
                .crc32c .x64 r5 r8 r9
              else
                if idx < 186 then
                  .fmovXD r8 r16
                else
                  .crc32c .x64 r8 r31 r8
            else
              if idx < 188 then
                .umovD r9 r16 l1
              else
                if idx < 189 then
                  .crc32c .x64 r6 r8 r9
                else
                  .logicReg true .orrOp .lsl false r0 r31 r10 0
          else
            if idx < 193 then
              if idx < 191 then
                .ldpGP true .signedOffset r20 r19 r31 0x50
              else
                if idx < 192 then
                  .ldpGP true .signedOffset r22 r21 r31 0x40
                else
                  .ldpGP true .signedOffset r24 r23 r31 0x30
            else
              if idx < 195 then
                if idx < 194 then
                  .ldpGP true .signedOffset r26 r25 r31 0x20
                else
                  .ldpGP true .signedOffset r28 r27 r31 0x10
              else
                if idx < 196 then
                  .ldpD .postIndex r9 r8 r31 0x60
                else
                  .b 0x0

set_option maxRecDepth 8192 in
private theorem hwFold6Loop_decode_ok :
    checkWordsAux hwFold6LoopWords hwFold6LoopInsn 197 = true := rfl

private theorem hwFold6Loop_decode_cert (idx : Nat) (hsz : idx < hwFold6LoopWords.size)
    (hlt : idx < 197) :
    Arm64.decode (hwFold6LoopWords[idx]'hsz) = some (hwFold6LoopInsn idx) :=
  checkWordsAux_spec hwFold6LoopWords hwFold6LoopInsn 197 hwFold6Loop_decode_ok idx hsz hlt


/-! ### `hwFold6` (186 instructions) -/

def hwFold6Words : Array UInt32 := #[
  0xd10283ff, 0xa90567fa, 0xa9065ff8, 0xa90757f6, 0xa9084ff4, 0xa9097bfd, 0x910243fd, 0xaa0303e9, -- 0..7
  0xaa0103e8, 0xd379e065, 0x9100602a, 0x8b02014e, 0x8b0501cd, 0xa94031cb, 0xa94141cf, 0xd37df063, -- 8..15
  0xd37ae524, 0xa94205d1, 0x8b090526, 0xd37ae4c6, 0xd378dd27, 0xa94351d3, 0x8b090935, 0x8b020089, -- 16..23
  0x8b090156, 0xa94062d7, 0xd37ae6aa, 0x9acb5c0b, 0x9acc5d6b, 0x9acf5d6b, 0xa9413ecc, 0x9ad05d6b, -- 24..31
  0x9ad15d6b, 0x9ac15d6b, 0x9ad35d6b, 0xa94246d0, 0x9ad45d6b, 0x9ad75fe0, 0x9ad85c00, 0x9acc5c0c, -- 32..39
  0xa94306c0, 0x9acf5d8c, 0x9ad05d8c, 0x9ad15d8c, 0x9ac05d8c, 0xa94041af, 0x9ac15d8c, 0x9acf5fe0, -- 40..47
  0x8b0601d3, 0xa943066f, 0x8b0701d1, 0x8b0a01ce, 0x90000014, 0xf9400294, 0x90000015, 0xf94002b5, -- 48..55
  0xfd400280, 0x6d400a61, 0x0ee0e021, 0x4e183c34, 0x9e660036, 0xfd4002a1, 0x0ee1e042, 0x90000015, -- 56..63
  0xf94002b5, 0x4e183c57, 0x9e660058, 0x90000019, 0xf9400339, 0xfd4002a2, 0x6d411263, 0x0ee2e066, -- 64..71
  0xfd400323, 0x90000015, 0xf94002b5, 0x90000019, 0xf9400339, 0x0ee3e087, 0xfd4002a4, 0x6d424265, -- 72..79
  0x0ee4e0b1, 0xfd400325, 0x0ee5e210, 0x2e261e32, 0x2e271e13, 0x2e321e72, 0x9e660253, 0xca180273, -- 80..87
  0xca0f02cf, 0xca0f026f, 0x4ed17a10, 0x4ec678e6, 0x6e261e06, 0x9ad05c00, 0x6e0640c7, 0x2e271cc6, -- 88..95
  0x9e6600d0, 0xca170210, 0xca010281, 0xca010210, 0x6d401e26, 0x0ee0e0c6, 0x4e183cc1, 0x9e6600d3, -- 96..103
  0x0ee1e0e6, 0x4e183cd4, 0x9e6600d5, 0x6d411e26, 0x0ee2e0c6, 0x0ee3e0e7, 0xa9415db6, 0x9ad65c00, -- 104..111
  0x6d424630, 0x0ee4e210, 0x0ee5e231, 0x2e261e12, 0x2e271e33, 0x2e321e72, 0x9e660256, 0xca1502d5, -- 112..119
  0x9ad75c00, 0xa9425db6, 0x9ad65c16, 0xa9436220, 0xca000271, 0xca1102b1, 0x4ed07a30, 0x4ec678e6, -- 120..127
  0x6e261e06, 0x6e0640c7, 0x2e271cc6, 0x9e6600c0, 0xca140000, 0xca180021, 0xca010000, 0x9ad75ec1, -- 128..135
  0xa94335b3, 0x9ad35c21, 0x6d401dc6, 0x0ee0e0c0, 0x9acd5c2d, 0x4e183c01, 0x9e660013, 0x0ee1e0e0, -- 136..143
  0x4e183c14, 0x9e660015, 0x6d4105c0, 0x0ee2e000, 0x0ee3e021, 0x6d420dc2, 0x0ee4e042, 0x0ee5e063, -- 144..151
  0x2e201c44, 0x2e211c65, 0x2e241ca4, 0x9e660096, 0xca1502d5, 0xa94339d6, 0xca160273, 0xca1302b3, -- 152..159
  0x4ec27862, 0x4ec07820, 0x6e201c40, 0x6e004001, 0x2e211c00, 0x9e660015, 0xca1402b4, 0xca0e002e, -- 160..167
  0xca0e028e, 0xf90003ea, 0x2901b7ec, 0xb9000beb, 0xa903bbf3, 0x91010041, 0xa90283f1, 0xa901c3ef, -- 168..175
  0xaa0803e0, 0xaa0903e2, 0x94000000, 0xa9497bfd, 0xa9484ff4, 0xa94757f6, 0xa9465ff8, 0xa94567fa, -- 176..183
  0x910283ff, 0xd65f03c0 -- 184..185
]

set_option maxRecDepth 8192 in
theorem hwFold6Words_size : hwFold6Words.size = 186 := rfl

def hwFold6Branches : List BranchReloc := [
  { idx := 178, isCall := true, target := .fnHwFold6Loop }
]

def hwFold6Gots : List GotReloc := [
  { idx := 52, rd := ⟨20, by decide⟩, target := .gKFold384_1 },
  { idx := 54, rd := ⟨21, by decide⟩, target := .gKFold384_2 },
  { idx := 63, rd := ⟨21, by decide⟩, target := .gKFold256_1 },
  { idx := 67, rd := ⟨25, by decide⟩, target := .gKFold256_2 },
  { idx := 73, rd := ⟨21, by decide⟩, target := .gKFold128_1 },
  { idx := 75, rd := ⟨25, by decide⟩, target := .gKFold128_2 }
]

def hwFold6Insn (idx : Nat) : Arm64.Instr :=
  if idx < 93 then
    if idx < 46 then
      if idx < 23 then
        if idx < 11 then
          if idx < 5 then
            if idx < 2 then
              if idx < 1 then
                .addSubImm true true false r31 r31 0xa0
              else
                .stpGP true .signedOffset r26 r25 r31 0x50
            else
              if idx < 3 then
                .stpGP true .signedOffset r24 r23 r31 0x60
              else
                if idx < 4 then
                  .stpGP true .signedOffset r22 r21 r31 0x70
                else
                  .stpGP true .signedOffset r20 r19 r31 0x80
          else
            if idx < 8 then
              if idx < 6 then
                .stpGP true .signedOffset r29 r30 r31 0x90
              else
                if idx < 7 then
                  .addSubImm true false false r29 r31 0x90
                else
                  .logicReg true .orrOp .lsl false r9 r31 r3 0
            else
              if idx < 9 then
                .logicReg true .orrOp .lsl false r8 r31 r1 0
              else
                if idx < 10 then
                  .ubfm true r5 r3 57 56
                else
                  .addSubImm true false false r10 r1 0x18
        else
          if idx < 17 then
            if idx < 14 then
              if idx < 12 then
                .addSubReg true false false .lsl r14 r10 r2 0
              else
                if idx < 13 then
                  .addSubReg true false false .lsl r13 r14 r5 0
                else
                  .ldpGP true .signedOffset r11 r12 r14 0x0
            else
              if idx < 15 then
                .ldpGP true .signedOffset r15 r16 r14 0x10
              else
                if idx < 16 then
                  .ubfm true r3 r3 61 60
                else
                  .ubfm true r4 r9 58 57
          else
            if idx < 20 then
              if idx < 18 then
                .ldpGP true .signedOffset r17 r1 r14 0x20
              else
                if idx < 19 then
                  .addSubReg true false false .lsl r6 r9 r9 1
                else
                  .ubfm true r6 r6 58 57
            else
              if idx < 21 then
                .ubfm true r7 r9 56 55
              else
                if idx < 22 then
                  .ldpGP true .signedOffset r19 r20 r14 0x30
                else
                  .addSubReg true false false .lsl r21 r9 r9 2
      else
        if idx < 34 then
          if idx < 28 then
            if idx < 25 then
              if idx < 24 then
                .addSubReg true false false .lsl r9 r4 r2 0
              else
                .addSubReg true false false .lsl r22 r10 r9 0
            else
              if idx < 26 then
                .ldpGP true .signedOffset r23 r24 r22 0x0
              else
                if idx < 27 then
                  .ubfm true r10 r21 58 57
                else
                  .crc32c .x64 r11 r0 r11
          else
            if idx < 31 then
              if idx < 29 then
                .crc32c .x64 r11 r11 r12
              else
                if idx < 30 then
                  .crc32c .x64 r11 r11 r15
                else
                  .ldpGP true .signedOffset r12 r15 r22 0x10
            else
              if idx < 32 then
                .crc32c .x64 r11 r11 r16
              else
                if idx < 33 then
                  .crc32c .x64 r11 r11 r17
                else
                  .crc32c .x64 r11 r11 r1
        else
          if idx < 40 then
            if idx < 37 then
              if idx < 35 then
                .crc32c .x64 r11 r11 r19
              else
                if idx < 36 then
                  .ldpGP true .signedOffset r16 r17 r22 0x20
                else
                  .crc32c .x64 r11 r11 r20
            else
              if idx < 38 then
                .crc32c .x64 r0 r31 r23
              else
                if idx < 39 then
                  .crc32c .x64 r0 r0 r24
                else
                  .crc32c .x64 r12 r0 r12
          else
            if idx < 43 then
              if idx < 41 then
                .ldpGP true .signedOffset r0 r1 r22 0x30
              else
                if idx < 42 then
                  .crc32c .x64 r12 r12 r15
                else
                  .crc32c .x64 r12 r12 r16
            else
              if idx < 44 then
                .crc32c .x64 r12 r12 r17
              else
                if idx < 45 then
                  .crc32c .x64 r12 r12 r0
                else
                  .ldpGP true .signedOffset r15 r16 r13 0x0
    else
      if idx < 69 then
        if idx < 57 then
          if idx < 51 then
            if idx < 48 then
              if idx < 47 then
                .crc32c .x64 r12 r12 r1
              else
                .crc32c .x64 r0 r31 r15
            else
              if idx < 49 then
                .addSubReg true false false .lsl r19 r14 r6 0
              else
                if idx < 50 then
                  .ldpGP true .signedOffset r15 r1 r19 0x30
                else
                  .addSubReg true false false .lsl r17 r14 r7 0
          else
            if idx < 54 then
              if idx < 52 then
                .addSubReg true false false .lsl r14 r14 r10 0
              else
                if idx < 53 then
                  .adrp r20 0x0
                else
                  .ldrUImm .x64 r20 r20 0x0
            else
              if idx < 55 then
                .adrp r21 0x0
              else
                if idx < 56 then
                  .ldrUImm .x64 r21 r21 0x0
                else
                  .ldrDImm r0 r20 0x0
        else
          if idx < 63 then
            if idx < 60 then
              if idx < 58 then
                .ldpD .signedOffset r1 r2 r19 0x0
              else
                if idx < 59 then
                  .pmull1Q r1 r1 r0
                else
                  .umovD r20 r1 l1
            else
              if idx < 61 then
                .fmovXD r22 r1
              else
                if idx < 62 then
                  .ldrDImm r1 r21 0x0
                else
                  .pmull1Q r2 r2 r1
          else
            if idx < 66 then
              if idx < 64 then
                .adrp r21 0x0
              else
                if idx < 65 then
                  .ldrUImm .x64 r21 r21 0x0
                else
                  .umovD r23 r2 l1
            else
              if idx < 67 then
                .fmovXD r24 r2
              else
                if idx < 68 then
                  .adrp r25 0x0
                else
                  .ldrUImm .x64 r25 r25 0x0
      else
        if idx < 81 then
          if idx < 75 then
            if idx < 72 then
              if idx < 70 then
                .ldrDImm r2 r21 0x0
              else
                if idx < 71 then
                  .ldpD .signedOffset r3 r4 r19 0x10
                else
                  .pmull1Q r6 r3 r2
            else
              if idx < 73 then
                .ldrDImm r3 r25 0x0
              else
                if idx < 74 then
                  .adrp r21 0x0
                else
                  .ldrUImm .x64 r21 r21 0x0
          else
            if idx < 78 then
              if idx < 76 then
                .adrp r25 0x0
              else
                if idx < 77 then
                  .ldrUImm .x64 r25 r25 0x0
                else
                  .pmull1Q r7 r4 r3
            else
              if idx < 79 then
                .ldrDImm r4 r21 0x0
              else
                if idx < 80 then
                  .ldpD .signedOffset r5 r16 r19 0x20
                else
                  .pmull1Q r17 r5 r4
        else
          if idx < 87 then
            if idx < 84 then
              if idx < 82 then
                .ldrDImm r5 r25 0x0
              else
                if idx < 83 then
                  .pmull1Q r16 r16 r5
                else
                  .eorVec false r18 r17 r6
            else
              if idx < 85 then
                .eorVec false r19 r16 r7
              else
                if idx < 86 then
                  .eorVec false r18 r19 r18
                else
                  .fmovXD r19 r18
          else
            if idx < 90 then
              if idx < 88 then
                .logicReg true .eorOp .lsl false r19 r19 r24 0
              else
                if idx < 89 then
                  .logicReg true .eorOp .lsl false r15 r22 r15 0
                else
                  .logicReg true .eorOp .lsl false r15 r19 r15 0
            else
              if idx < 91 then
                .zip2_2D r16 r16 r17
              else
                if idx < 92 then
                  .zip2_2D r6 r7 r6
                else
                  .eorVec true r6 r16 r6
  else
    if idx < 139 then
      if idx < 116 then
        if idx < 104 then
          if idx < 98 then
            if idx < 95 then
              if idx < 94 then
                .crc32c .x64 r0 r0 r16
              else
                .ext16B r7 r6 r6 c8
            else
              if idx < 96 then
                .eorVec false r6 r6 r7
              else
                if idx < 97 then
                  .fmovXD r16 r6
                else
                  .logicReg true .eorOp .lsl false r16 r16 r23 0
          else
            if idx < 101 then
              if idx < 99 then
                .logicReg true .eorOp .lsl false r1 r20 r1 0
              else
                if idx < 100 then
                  .logicReg true .eorOp .lsl false r16 r16 r1 0
                else
                  .ldpD .signedOffset r6 r7 r17 0x0
            else
              if idx < 102 then
                .pmull1Q r6 r6 r0
              else
                if idx < 103 then
                  .umovD r1 r6 l1
                else
                  .fmovXD r19 r6
        else
          if idx < 110 then
            if idx < 107 then
              if idx < 105 then
                .pmull1Q r6 r7 r1
              else
                if idx < 106 then
                  .umovD r20 r6 l1
                else
                  .fmovXD r21 r6
            else
              if idx < 108 then
                .ldpD .signedOffset r6 r7 r17 0x10
              else
                if idx < 109 then
                  .pmull1Q r6 r6 r2
                else
                  .pmull1Q r7 r7 r3
          else
            if idx < 113 then
              if idx < 111 then
                .ldpGP true .signedOffset r22 r23 r13 0x10
              else
                if idx < 112 then
                  .crc32c .x64 r0 r0 r22
                else
                  .ldpD .signedOffset r16 r17 r17 0x20
            else
              if idx < 114 then
                .pmull1Q r16 r16 r4
              else
                if idx < 115 then
                  .pmull1Q r17 r17 r5
                else
                  .eorVec false r18 r16 r6
      else
        if idx < 127 then
          if idx < 121 then
            if idx < 118 then
              if idx < 117 then
                .eorVec false r19 r17 r7
              else
                .eorVec false r18 r19 r18
            else
              if idx < 119 then
                .fmovXD r22 r18
              else
                if idx < 120 then
                  .logicReg true .eorOp .lsl false r21 r22 r21 0
                else
                  .crc32c .x64 r0 r0 r23
          else
            if idx < 124 then
              if idx < 122 then
                .ldpGP true .signedOffset r22 r23 r13 0x20
              else
                if idx < 123 then
                  .crc32c .x64 r22 r0 r22
                else
                  .ldpGP true .signedOffset r0 r24 r17 0x30
            else
              if idx < 125 then
                .logicReg true .eorOp .lsl false r17 r19 r0 0
              else
                if idx < 126 then
                  .logicReg true .eorOp .lsl false r17 r21 r17 0
                else
                  .zip2_2D r16 r17 r16
        else
          if idx < 133 then
            if idx < 130 then
              if idx < 128 then
                .zip2_2D r6 r7 r6
              else
                if idx < 129 then
                  .eorVec true r6 r16 r6
                else
                  .ext16B r7 r6 r6 c8
            else
              if idx < 131 then
                .eorVec false r6 r6 r7
              else
                if idx < 132 then
                  .fmovXD r0 r6
                else
                  .logicReg true .eorOp .lsl false r0 r0 r20 0
          else
            if idx < 136 then
              if idx < 134 then
                .logicReg true .eorOp .lsl false r1 r1 r24 0
              else
                if idx < 135 then
                  .logicReg true .eorOp .lsl false r0 r0 r1 0
                else
                  .crc32c .x64 r1 r22 r23
            else
              if idx < 137 then
                .ldpGP true .signedOffset r19 r13 r13 0x30
              else
                if idx < 138 then
                  .crc32c .x64 r1 r1 r19
                else
                  .ldpD .signedOffset r6 r7 r14 0x0
    else
      if idx < 162 then
        if idx < 150 then
          if idx < 144 then
            if idx < 141 then
              if idx < 140 then
                .pmull1Q r0 r6 r0
              else
                .crc32c .x64 r13 r1 r13
            else
              if idx < 142 then
                .umovD r1 r0 l1
              else
                if idx < 143 then
                  .fmovXD r19 r0
                else
                  .pmull1Q r0 r7 r1
          else
            if idx < 147 then
              if idx < 145 then
                .umovD r20 r0 l1
              else
                if idx < 146 then
                  .fmovXD r21 r0
                else
                  .ldpD .signedOffset r0 r1 r14 0x10
            else
              if idx < 148 then
                .pmull1Q r0 r0 r2
              else
                if idx < 149 then
                  .pmull1Q r1 r1 r3
                else
                  .ldpD .signedOffset r2 r3 r14 0x20
        else
          if idx < 156 then
            if idx < 153 then
              if idx < 151 then
                .pmull1Q r2 r2 r4
              else
                if idx < 152 then
                  .pmull1Q r3 r3 r5
                else
                  .eorVec false r4 r2 r0
            else
              if idx < 154 then
                .eorVec false r5 r3 r1
              else
                if idx < 155 then
                  .eorVec false r4 r5 r4
                else
                  .fmovXD r22 r4
          else
            if idx < 159 then
              if idx < 157 then
                .logicReg true .eorOp .lsl false r21 r22 r21 0
              else
                if idx < 158 then
                  .ldpGP true .signedOffset r22 r14 r14 0x30
                else
                  .logicReg true .eorOp .lsl false r19 r19 r22 0
            else
              if idx < 160 then
                .logicReg true .eorOp .lsl false r19 r21 r19 0
              else
                if idx < 161 then
                  .zip2_2D r2 r3 r2
                else
                  .zip2_2D r0 r1 r0
      else
        if idx < 174 then
          if idx < 168 then
            if idx < 165 then
              if idx < 163 then
                .eorVec true r0 r2 r0
              else
                if idx < 164 then
                  .ext16B r1 r0 r0 c8
                else
                  .eorVec false r0 r0 r1
            else
              if idx < 166 then
                .fmovXD r21 r0
              else
                if idx < 167 then
                  .logicReg true .eorOp .lsl false r20 r21 r20 0
                else
                  .logicReg true .eorOp .lsl false r14 r1 r14 0
          else
            if idx < 171 then
              if idx < 169 then
                .logicReg true .eorOp .lsl false r14 r20 r14 0
              else
                if idx < 170 then
                  .strUImm .x64 r10 r31 0x0
                else
                  .stpGP false .signedOffset r12 r13 r31 0xc
            else
              if idx < 172 then
                .strUImm .w32 r11 r31 0x8
              else
                if idx < 173 then
                  .stpGP true .signedOffset r19 r14 r31 0x38
                else
                  .addSubImm true false false r1 r2 0x40
        else
          if idx < 180 then
            if idx < 177 then
              if idx < 175 then
                .stpGP true .signedOffset r17 r0 r31 0x28
              else
                if idx < 176 then
                  .stpGP true .signedOffset r15 r16 r31 0x18
                else
                  .logicReg true .orrOp .lsl false r0 r31 r8 0
            else
              if idx < 178 then
                .logicReg true .orrOp .lsl false r2 r31 r9 0
              else
                if idx < 179 then
                  .bl 0x0
                else
                  .ldpGP true .signedOffset r29 r30 r31 0x90
          else
            if idx < 183 then
              if idx < 181 then
                .ldpGP true .signedOffset r20 r19 r31 0x80
              else
                if idx < 182 then
                  .ldpGP true .signedOffset r22 r21 r31 0x70
                else
                  .ldpGP true .signedOffset r24 r23 r31 0x60
            else
              if idx < 184 then
                .ldpGP true .signedOffset r26 r25 r31 0x50
              else
                if idx < 185 then
                  .addSubImm true false false r31 r31 0xa0
                else
                  .ret r30

set_option maxRecDepth 8192 in
private theorem hwFold6_decode_ok :
    checkWordsAux hwFold6Words hwFold6Insn 186 = true := rfl

private theorem hwFold6_decode_cert (idx : Nat) (hsz : idx < hwFold6Words.size)
    (hlt : idx < 186) :
    Arm64.decode (hwFold6Words[idx]'hsz) = some (hwFold6Insn idx) :=
  checkWordsAux_spec hwFold6Words hwFold6Insn 186 hwFold6_decode_ok idx hsz hlt


/-! ### `rawExtendHwMulti` (119 instructions) -/

def rawExtendHwMultiWords : Array UInt32 := #[
  0xa9bb67fa, 0xa9015ff8, 0xa90257f6, 0xa9034ff4, 0xa9047bfd, 0x910103fd, 0xaa0303f4, 0xaa0203f5, -- 0..7
  0xaa0103f3, 0xaa0003e1, 0xf10bfc7f, 0x54000468, 0x12003e88, 0x52955569, 0x1b097d08, 0x53157d0a, -- 8..15
  0xd37f7d40, 0xd37c7d48, 0x8b0a0009, 0xd37ced36, 0x8b150109, 0xeb15013f, 0x54000589, 0x52800002, -- 16..23
  0x52800003, 0xd37b7d4a, 0x8b15026b, 0x910022ac, 0x9100616b, 0xa940396d, 0x9acd5c2d, 0x9ace5da1, -- 24..31
  0x8b08016d, 0xa94035ae, 0x9ace5c4e, 0x9acd5dc2, 0x8b0a016d, 0xa94035ae, 0x9ace5c6e, 0x9acd5dc3, -- 32..39
  0x9100218d, 0x9100418c, 0x9100416b, 0xeb0901bf, 0x54fffe23, 0x14000017, 0xb201f3f7, 0xf2955577, -- 40..47
  0x9bd77e88, 0xd348fd03, 0x8b030468, 0xd379e118, 0xcb180299, 0xaa0103e0, 0xaa1303e1, 0xaa1503e2, -- 48..55
  0x94000000, 0xaa0003e8, 0x8b150316, 0xf1017f3f, 0x54000188, 0x8b150282, 0xaa1303e0, 0xaa1603e1, -- 56..63
  0xaa0803e3, 0x14000030, 0x52800003, 0x52800002, 0x94000000, 0xaa0003e3, 0x8b1502c1, 0x14000028, -- 64..71
  0x9bd77f29, 0xd345fd2b, 0xd37ff960, 0xd37ced69, 0x8b0b000a, 0xd37ced57, 0x8b16012a, 0xeb0a02df, -- 72..79
  0x54000322, 0x52800002, 0x52800003, 0xd37be96b, 0x8b16026c, 0x8b1802ad, 0x910021ad, 0x9100618c, -- 80..87
  0xa9403d8e, 0x9ace5d08, 0x9acf5d08, 0x8b09018e, 0xa94039cf, 0x9acf5c4f, 0x9ace5de2, 0x8b0b018e, -- 88..95
  0xa94039cf, 0x9acf5c6f, 0x9ace5de3, 0x910021ae, 0x910041ad, 0x9100418c, 0xeb0a01df, 0x54fffe23, -- 96..103
  0x14000003, 0x52800003, 0x52800002, 0xaa0803e1, 0x94000000, 0xaa0003e3, 0x8b1602e1, 0x8b150282, -- 104..111
  0xaa1303e0, 0xa9447bfd, 0xa9434ff4, 0xa94257f6, 0xa9415ff8, 0xa8c567fa, 0x14000000 -- 112..118
]

set_option maxRecDepth 8192 in
theorem rawExtendHwMultiWords_size : rawExtendHwMultiWords.size = 119 := rfl

def rawExtendHwMultiBranches : List BranchReloc := [
  { idx := 56, isCall := true, target := .fnHwFold6 },
  { idx := 68, isCall := true, target := .fnCombine3 },
  { idx := 108, isCall := true, target := .fnCombine3 },
  { idx := 118, isCall := false, target := .fnHwLoop }
]

def rawExtendHwMultiGots : List GotReloc := []

def rawExtendHwMultiInsn (idx : Nat) : Arm64.Instr :=
  if idx < 59 then
    if idx < 29 then
      if idx < 14 then
        if idx < 7 then
          if idx < 3 then
            if idx < 1 then
              .stpGP true .preIndex r26 r25 r31 0xffffffffffffffb0
            else
              if idx < 2 then
                .stpGP true .signedOffset r24 r23 r31 0x10
              else
                .stpGP true .signedOffset r22 r21 r31 0x20
          else
            if idx < 5 then
              if idx < 4 then
                .stpGP true .signedOffset r20 r19 r31 0x30
              else
                .stpGP true .signedOffset r29 r30 r31 0x40
            else
              if idx < 6 then
                .addSubImm true false false r29 r31 0x40
              else
                .logicReg true .orrOp .lsl false r20 r31 r3 0
        else
          if idx < 10 then
            if idx < 8 then
              .logicReg true .orrOp .lsl false r21 r31 r2 0
            else
              if idx < 9 then
                .logicReg true .orrOp .lsl false r19 r31 r1 0
              else
                .logicReg true .orrOp .lsl false r1 r31 r0 0
          else
            if idx < 12 then
              if idx < 11 then
                .addSubImm true true true r31 r3 0x2ff
              else
                .bCond c8 0x8c
            else
              if idx < 13 then
                .logicImm false .andOp r8 r20 0xffff
              else
                .movWide false .movz r9 0xaaab 0
      else
        if idx < 21 then
          if idx < 17 then
            if idx < 15 then
              .madd false r8 r8 r9 r31
            else
              if idx < 16 then
                .ubfm false r10 r8 21 31
              else
                .ubfm true r0 r10 63 31
          else
            if idx < 19 then
              if idx < 18 then
                .ubfm true r8 r10 60 31
              else
                .addSubReg true false false .lsl r9 r0 r10 0
            else
              if idx < 20 then
                .ubfm true r22 r9 60 59
              else
                .addSubReg true false false .lsl r9 r8 r21 0
        else
          if idx < 25 then
            if idx < 23 then
              if idx < 22 then
                .addSubReg true true true .lsl r31 r9 r21 0
              else
                .bCond c9 0xb0
            else
              if idx < 24 then
                .movWide false .movz r2 0x0 0
              else
                .movWide false .movz r3 0x0 0
          else
            if idx < 27 then
              if idx < 26 then
                .ubfm true r10 r10 59 31
              else
                .addSubReg true false false .lsl r11 r19 r21 0
            else
              if idx < 28 then
                .addSubImm true false false r12 r21 0x8
              else
                .addSubImm true false false r11 r11 0x18
    else
      if idx < 44 then
        if idx < 36 then
          if idx < 32 then
            if idx < 30 then
              .ldpGP true .signedOffset r13 r14 r11 0x0
            else
              if idx < 31 then
                .crc32c .x64 r13 r1 r13
              else
                .crc32c .x64 r1 r13 r14
          else
            if idx < 34 then
              if idx < 33 then
                .addSubReg true false false .lsl r13 r11 r8 0
              else
                .ldpGP true .signedOffset r14 r13 r13 0x0
            else
              if idx < 35 then
                .crc32c .x64 r14 r2 r14
              else
                .crc32c .x64 r2 r14 r13
        else
          if idx < 40 then
            if idx < 38 then
              if idx < 37 then
                .addSubReg true false false .lsl r13 r11 r10 0
              else
                .ldpGP true .signedOffset r14 r13 r13 0x0
            else
              if idx < 39 then
                .crc32c .x64 r14 r3 r14
              else
                .crc32c .x64 r3 r14 r13
          else
            if idx < 42 then
              if idx < 41 then
                .addSubImm true false false r13 r12 0x8
              else
                .addSubImm true false false r12 r12 0x10
            else
              if idx < 43 then
                .addSubImm true false false r11 r11 0x10
              else
                .addSubReg true true true .lsl r31 r13 r9 0
      else
        if idx < 51 then
          if idx < 47 then
            if idx < 45 then
              .bCond c3 0xffffffffffffffc4
            else
              if idx < 46 then
                .b 0x5c
              else
                .logicImm true .orrOp r23 r31 0xaaaaaaaaaaaaaaaa
          else
            if idx < 49 then
              if idx < 48 then
                .movWide true .movk r23 0xaaab 0
              else
                .umulh r8 r20 r23
            else
              if idx < 50 then
                .ubfm true r3 r8 8 63
              else
                .addSubReg true false false .lsl r8 r3 r3 1
        else
          if idx < 55 then
            if idx < 53 then
              if idx < 52 then
                .ubfm true r24 r8 57 56
              else
                .addSubReg true true false .lsl r25 r20 r24 0
            else
              if idx < 54 then
                .logicReg true .orrOp .lsl false r0 r31 r1 0
              else
                .logicReg true .orrOp .lsl false r1 r31 r19 0
          else
            if idx < 57 then
              if idx < 56 then
                .logicReg true .orrOp .lsl false r2 r31 r21 0
              else
                .bl 0x0
            else
              if idx < 58 then
                .logicReg true .orrOp .lsl false r8 r31 r0 0
              else
                .addSubReg true false false .lsl r22 r24 r21 0
  else
    if idx < 89 then
      if idx < 74 then
        if idx < 66 then
          if idx < 62 then
            if idx < 60 then
              .addSubImm true true true r31 r25 0x5f
            else
              if idx < 61 then
                .bCond c8 0x30
              else
                .addSubReg true false false .lsl r2 r20 r21 0
          else
            if idx < 64 then
              if idx < 63 then
                .logicReg true .orrOp .lsl false r0 r31 r19 0
              else
                .logicReg true .orrOp .lsl false r1 r31 r22 0
            else
              if idx < 65 then
                .logicReg true .orrOp .lsl false r3 r31 r8 0
              else
                .b 0xc0
        else
          if idx < 70 then
            if idx < 68 then
              if idx < 67 then
                .movWide false .movz r3 0x0 0
              else
                .movWide false .movz r2 0x0 0
            else
              if idx < 69 then
                .bl 0x0
              else
                .logicReg true .orrOp .lsl false r3 r31 r0 0
          else
            if idx < 72 then
              if idx < 71 then
                .addSubReg true false false .lsl r1 r22 r21 0
              else
                .b 0xa0
            else
              if idx < 73 then
                .umulh r9 r25 r23
              else
                .ubfm true r11 r9 5 63
      else
        if idx < 81 then
          if idx < 77 then
            if idx < 75 then
              .ubfm true r0 r11 63 62
            else
              if idx < 76 then
                .ubfm true r9 r11 60 59
              else
                .addSubReg true false false .lsl r10 r0 r11 0
          else
            if idx < 79 then
              if idx < 78 then
                .ubfm true r23 r10 60 59
              else
                .addSubReg true false false .lsl r10 r9 r22 0
            else
              if idx < 80 then
                .addSubReg true true true .lsl r31 r22 r10 0
              else
                .bCond c2 0x64
        else
          if idx < 85 then
            if idx < 83 then
              if idx < 82 then
                .movWide false .movz r2 0x0 0
              else
                .movWide false .movz r3 0x0 0
            else
              if idx < 84 then
                .ubfm true r11 r11 59 58
              else
                .addSubReg true false false .lsl r12 r19 r22 0
          else
            if idx < 87 then
              if idx < 86 then
                .addSubReg true false false .lsl r13 r21 r24 0
              else
                .addSubImm true false false r13 r13 0x8
            else
              if idx < 88 then
                .addSubImm true false false r12 r12 0x18
              else
                .ldpGP true .signedOffset r14 r15 r12 0x0
    else
      if idx < 104 then
        if idx < 96 then
          if idx < 92 then
            if idx < 90 then
              .crc32c .x64 r8 r8 r14
            else
              if idx < 91 then
                .crc32c .x64 r8 r8 r15
              else
                .addSubReg true false false .lsl r14 r12 r9 0
          else
            if idx < 94 then
              if idx < 93 then
                .ldpGP true .signedOffset r15 r14 r14 0x0
              else
                .crc32c .x64 r15 r2 r15
            else
              if idx < 95 then
                .crc32c .x64 r2 r15 r14
              else
                .addSubReg true false false .lsl r14 r12 r11 0
        else
          if idx < 100 then
            if idx < 98 then
              if idx < 97 then
                .ldpGP true .signedOffset r15 r14 r14 0x0
              else
                .crc32c .x64 r15 r3 r15
            else
              if idx < 99 then
                .crc32c .x64 r3 r15 r14
              else
                .addSubImm true false false r14 r13 0x8
          else
            if idx < 102 then
              if idx < 101 then
                .addSubImm true false false r13 r13 0x10
              else
                .addSubImm true false false r12 r12 0x10
            else
              if idx < 103 then
                .addSubReg true true true .lsl r31 r14 r10 0
              else
                .bCond c3 0xffffffffffffffc4
      else
        if idx < 111 then
          if idx < 107 then
            if idx < 105 then
              .b 0xc
            else
              if idx < 106 then
                .movWide false .movz r3 0x0 0
              else
                .movWide false .movz r2 0x0 0
          else
            if idx < 109 then
              if idx < 108 then
                .logicReg true .orrOp .lsl false r1 r31 r8 0
              else
                .bl 0x0
            else
              if idx < 110 then
                .logicReg true .orrOp .lsl false r3 r31 r0 0
              else
                .addSubReg true false false .lsl r1 r23 r22 0
        else
          if idx < 115 then
            if idx < 113 then
              if idx < 112 then
                .addSubReg true false false .lsl r2 r20 r21 0
              else
                .logicReg true .orrOp .lsl false r0 r31 r19 0
            else
              if idx < 114 then
                .ldpGP true .signedOffset r29 r30 r31 0x40
              else
                .ldpGP true .signedOffset r20 r19 r31 0x30
          else
            if idx < 117 then
              if idx < 116 then
                .ldpGP true .signedOffset r22 r21 r31 0x20
              else
                .ldpGP true .signedOffset r24 r23 r31 0x10
            else
              if idx < 118 then
                .ldpGP true .postIndex r26 r25 r31 0x50
              else
                .b 0x0

set_option maxRecDepth 8192 in
private theorem rawExtendHwMulti_decode_ok :
    checkWordsAux rawExtendHwMultiWords rawExtendHwMultiInsn 119 = true := rfl

private theorem rawExtendHwMulti_decode_cert (idx : Nat) (hsz : idx < rawExtendHwMultiWords.size)
    (hlt : idx < 119) :
    Arm64.decode (rawExtendHwMultiWords[idx]'hsz) = some (rawExtendHwMultiInsn idx) :=
  checkWordsAux_spec rawExtendHwMultiWords rawExtendHwMultiInsn 119 rawExtendHwMulti_decode_ok idx hsz hlt


/-! ### `extendHwRaw` (427 instructions) -/

def extendHwRawWords : Array UInt32 := #[
  0xaa0203e3, 0x2a2003e8, 0xf1017c5f, 0x54000288, 0xf1007c7f, 0x54000348, 0xf1003c7f, 0x54000648, -- 0..7
  0xb40002c3, 0xf1001c7f, 0x54000e68, 0xf1000c7f, 0x54001228, 0x39406029, 0xf100047f, 0x54003320, -- 8..15
  0x3940642a, 0x2a0a2129, 0x1ac95508, 0xf1000c7f, 0x54000ce1, 0x39406829, 0x14000192, 0xa9bf7bfd, -- 16..23
  0x910003fd, 0xaa0803e0, 0xd2800002, 0x94000000, 0x2a2003e0, 0xa8c17bfd, 0xd65f03c0, 0xa9c1a42a, -- 24..31
  0x9aca5d08, 0x9ac95d08, 0xa941242a, 0x9aca5d08, 0x9ac95d08, 0xf100fc7f, 0x540004a8, 0xd1008069, -- 32..39
  0xf1003d3f, 0x54000768, 0xf100807f, 0x54000a00, 0xf1001d3f, 0x54001028, 0xf1000d3f, 0x540019a8, -- 40..47
  0x3940802a, 0xf100053f, 0x54000d09, 0x39408429, 0x2a092149, 0x1ac95508, 0xf100887f, 0x54001708, -- 48..55
  0x14000043, 0xa941a829, 0x9ac95d08, 0x9aca5d08, 0xf1004069, 0x540007c0, 0xf1001d3f, 0x54000928, -- 56..63
  0xf1000d3f, 0x54000f08, 0x3940a02a, 0xf100053f, 0x54000ac9, 0x3940a429, 0x2a092149, 0x1ac95508, -- 64..71
  0xf100487f, 0x54000649, 0x1400011b, 0xa9422829, 0x9ac95d08, 0x9aca5d08, 0xa9432829, 0x9ac95d08, -- 72..79
  0x9aca5d08, 0xd1010069, 0xf1003d3f, 0x54000468, 0xf101007f, 0x540004c0, 0xf1001d3f, 0x54000d68, -- 80..87
  0xf1000d3f, 0x540015a8, 0x3941002a, 0xf100053f, 0x540007c9, 0x39410429, 0x2a092149, 0x1ac95508, -- 88..95
  0xf101087f, 0x54000349, 0x39410829, 0x14000145, 0xa9422829, 0x9ac95d08, 0x9aca5d08, 0xf100c069, -- 96..103
  0x54000269, 0xf1001d3f, 0x54000c68, 0xf1000d3f, 0x54001488, 0x3940c02a, 0xf100053f, 0x54000569, -- 104..111
  0x3940c429, 0x2a092149, 0x1ac95508, 0xf100c87f, 0x54001548, 0x14000006, 0xa9442829, 0x9ac95d08, -- 112..119
  0x9aca5d08, 0xf1014069, 0x54000328, 0x2a2803e0, 0xd65f03c0, 0xf9400c29, 0x9ac95d08, 0xd1002069, -- 120..127
  0xf1000d3f, 0x540004a8, 0xf100053f, 0x54000d08, 0xf100207f, 0x54fffec0, 0x39408029, 0x14000121, -- 128..135
  0xf9401429, 0x9ac95d08, 0xd1006069, 0xf1000d3f, 0x54000988, 0xf100053f, 0x54001188, 0xf100607f, -- 136..143
  0x54fffd69, 0x3940c029, 0x14000116, 0xf1001d3f, 0x54000988, 0xf1000d3f, 0x54001148, 0x3941402a, -- 144..151
  0xf100053f, 0x54001828, 0x1aca5108, 0x2a2803e0, 0xd65f03c0, 0xb9401829, 0x1ac95908, 0x927f0469, -- 152..159
  0xf100113f, 0x54000a01, 0xf100107f, 0x54fffb00, 0x39407029, 0x14000103, 0xb9402029, 0x1ac95908, -- 160..167
  0x927f0869, 0xf100313f, 0x540009a1, 0xf100307f, 0x54fff9e9, 0x14000057, 0xf9401029, 0x9ac95d08, -- 168..175
  0xd100a069, 0xf1000d3f, 0x54000f08, 0xf100053f, 0x540015a8, 0xf100a07f, 0x54fff8a9, 0x3940a029, -- 176..183
  0x140000f0, 0xb9402829, 0x1ac95908, 0x528002c9, 0x8a090069, 0xf100513f, 0x54000ec1, 0xf100507f, -- 184..191
  0x54fff769, 0x14000071, 0xf9402029, 0x9ac95d08, 0xd1012069, 0xf1000d3f, 0x54000e68, 0xf100053f, -- 192..199
  0x540013e8, 0xf101207f, 0x54fff629, 0x39412029, 0x140000dc, 0xf9401829, 0x9ac95d08, 0xd100e069, -- 200..207
  0xf1000d3f, 0x54000e48, 0xf100053f, 0x54001348, 0xf100e07f, 0x54fff4c9, 0x3940e029, 0x140000d1, -- 208..215
  0xb9403029, 0x1ac95908, 0x927f0c69, 0xf100713f, 0x54000e01, 0xf100707f, 0x54fff3a9, 0x14000039, -- 216..223
  0xf9402829, 0x9ac95d08, 0xd1016069, 0xf1000d3f, 0x54000da8, 0xf100053f, 0x540011a8, 0xf101607f, -- 224..231
  0x54fff269, 0x39416029, 0x140000be, 0x79404029, 0x1ac95508, 0xf100287f, 0x54fff1a9, 0x39408829, -- 232..239
  0x140000b8, 0x79403829, 0x1ac95508, 0xf1001c7f, 0x54fff0e1, 0x39407829, 0x140000b2, 0x79404829, -- 240..247
  0x1ac95508, 0xf1003c7f, 0x54fff021, 0x14000082, 0xb9402029, 0x1ac95908, 0x528004c9, 0x8a090069, -- 248..255
  0xf100913f, 0x54000f01, 0xf100907f, 0x54ffef09, 0x39409029, 0x140000a3, 0xb9404029, 0x1ac95908, -- 256..263
  0x528008c9, 0x8a090069, 0xf101113f, 0x54000e81, 0xf101107f, 0x54ffedc9, 0x39411029, 0x14000099, -- 264..271
  0xb9403029, 0x1ac95908, 0x528006c9, 0x8a090069, 0xf100d13f, 0x54000e01, 0xf100d07f, 0x54ffec89, -- 272..279
  0x3940d029, 0x1400008f, 0x79406029, 0x1ac95508, 0xf100687f, 0x54ffebc9, 0x3940c829, 0x14000089, -- 280..287
  0xb9405029, 0x1ac95908, 0x52800ac9, 0x8a090069, 0xf101513f, 0x54000cc1, 0xf101507f, 0x54ffea89, -- 288..295
  0x39415029, 0x1400007f, 0xb9402829, 0x1ac95908, 0x528005c9, 0x8a090069, 0xf100b13f, 0x54000c41, -- 296..303
  0xf100b07f, 0x54ffe949, 0x3940b029, 0x14000075, 0x79405829, 0x1ac95508, 0xf100587f, 0x54ffe889, -- 304..311
  0x1400005d, 0xb9404829, 0x1ac95908, 0x528009c9, 0x8a090069, 0xf101313f, 0x54000b21, 0xf101307f, -- 312..319
  0x54ffe769, 0x39413029, 0x14000066, 0xb9403829, 0x1ac95908, 0x927f1069, 0xf100f13f, 0x54000ac1, -- 320..327
  0xf100f07f, 0x54ffe649, 0x3940f029, 0x1400005d, 0x79406829, 0x1ac95508, 0xf1007c7f, 0x54ffe581, -- 328..335
  0x14000039, 0xb9405829, 0x1ac95908, 0x927f1469, 0xf101713f, 0x540009c1, 0xf101707f, 0x54ffe489, -- 336..343
  0x39417029, 0x1400004f, 0x39414429, 0x2a092149, 0x1ac95508, 0xf101487f, 0x54ffe3a9, 0x39414829, -- 344..351
  0x14000048, 0x79405029, 0x1ac95508, 0xf100a87f, 0x54ffe2e9, 0x3940a829, 0x14000042, 0x79409029, -- 352..359
  0x1ac95508, 0xf101287f, 0x54ffe229, 0x39412829, 0x1400003c, 0x79407029, 0x1ac95508, 0xf100e87f, -- 360..367
  0x54ffe169, 0x3940e829, 0x14000036, 0x7940b029, 0x1ac95508, 0xf101687f, 0x54ffe0a9, 0x39416829, -- 368..375
  0x14000030, 0x79404829, 0x1ac95508, 0xf100987f, 0x54ffdfe9, 0x39409829, 0x1400002a, 0x79408829, -- 376..383
  0x1ac95508, 0xf101187f, 0x54ffdf29, 0x39411829, 0x14000024, 0x79406829, 0x1ac95508, 0xf100d87f, -- 384..391
  0x54ffde69, 0x3940d829, 0x1400001e, 0x7940a829, 0x1ac95508, 0xf101587f, 0x54ffdda9, 0x39415829, -- 392..399
  0x14000018, 0x79405829, 0x1ac95508, 0xf100b87f, 0x54ffdce9, 0x3940b829, 0x14000012, 0x79409829, -- 400..407
  0x1ac95508, 0xf101387f, 0x54ffdc29, 0x39413829, 0x1400000c, 0x79407829, 0x1ac95508, 0xf100fc7f, -- 408..415
  0x54ffdb61, 0x3940f829, 0x14000006, 0x7940b829, 0x1ac95508, 0xf1017c7f, 0x54ffdaa1, 0x39417829, -- 416..423
  0x1ac95108, 0x2a2803e0, 0xd65f03c0 -- 424..426
]

set_option maxRecDepth 8192 in
theorem extendHwRawWords_size : extendHwRawWords.size = 427 := rfl

def extendHwRawBranches : List BranchReloc := [
  { idx := 27, isCall := true, target := .fnRawExtendHwMulti }
]

def extendHwRawGots : List GotReloc := []

def extendHwRawInsn (idx : Nat) : Arm64.Instr :=
  if idx < 213 then
    if idx < 106 then
      if idx < 53 then
        if idx < 26 then
          if idx < 13 then
            if idx < 6 then
              if idx < 3 then
                if idx < 1 then
                  .logicReg true .orrOp .lsl false r3 r31 r2 0
                else
                  if idx < 2 then
                    .logicReg false .orrOp .lsl true r8 r31 r0 0
                  else
                    .addSubImm true true true r31 r2 0x5f
              else
                if idx < 4 then
                  .bCond c8 0x50
                else
                  if idx < 5 then
                    .addSubImm true true true r31 r3 0x1f
                  else
                    .bCond c8 0x68
            else
              if idx < 9 then
                if idx < 7 then
                  .addSubImm true true true r31 r3 0xf
                else
                  if idx < 8 then
                    .bCond c8 0xc8
                  else
                    .cbz true false r3 0x58
              else
                if idx < 11 then
                  if idx < 10 then
                    .addSubImm true true true r31 r3 0x7
                  else
                    .bCond c8 0x1cc
                else
                  if idx < 12 then
                    .addSubImm true true true r31 r3 0x3
                  else
                    .bCond c8 0x244
          else
            if idx < 19 then
              if idx < 16 then
                if idx < 14 then
                  .ldrUImm .b8 r9 r1 0x18
                else
                  if idx < 15 then
                    .addSubImm true true true r31 r3 0x1
                  else
                    .bCond c0 0x664
              else
                if idx < 17 then
                  .ldrUImm .b8 r10 r1 0x19
                else
                  if idx < 18 then
                    .logicReg false .orrOp .lsl false r9 r9 r10 8
                  else
                    .crc32c .h16 r8 r8 r9
            else
              if idx < 22 then
                if idx < 20 then
                  .addSubImm true true true r31 r3 0x3
                else
                  if idx < 21 then
                    .bCond c1 0x19c
                  else
                    .ldrUImm .b8 r9 r1 0x1a
              else
                if idx < 24 then
                  if idx < 23 then
                    .b 0x648
                  else
                    .stpGP true .preIndex r29 r30 r31 0xfffffffffffffff0
                else
                  if idx < 25 then
                    .addSubImm true false false r29 r31 0x0
                  else
                    .logicReg true .orrOp .lsl false r0 r31 r8 0
        else
          if idx < 39 then
            if idx < 32 then
              if idx < 29 then
                if idx < 27 then
                  .movWide true .movz r2 0x0 0
                else
                  if idx < 28 then
                    .bl 0x0
                  else
                    .logicReg false .orrOp .lsl true r0 r31 r0 0
              else
                if idx < 30 then
                  .ldpGP true .postIndex r29 r30 r31 0x10
                else
                  if idx < 31 then
                    .ret r30
                  else
                    .ldpGP true .preIndex r10 r9 r1 0x18
            else
              if idx < 35 then
                if idx < 33 then
                  .crc32c .x64 r8 r8 r10
                else
                  if idx < 34 then
                    .crc32c .x64 r8 r8 r9
                  else
                    .ldpGP true .signedOffset r10 r9 r1 0x10
              else
                if idx < 37 then
                  if idx < 36 then
                    .crc32c .x64 r8 r8 r10
                  else
                    .crc32c .x64 r8 r8 r9
                else
                  if idx < 38 then
                    .addSubImm true true true r31 r3 0x3f
                  else
                    .bCond c8 0x94
          else
            if idx < 46 then
              if idx < 42 then
                if idx < 40 then
                  .addSubImm true true false r9 r3 0x20
                else
                  if idx < 41 then
                    .addSubImm true true true r31 r9 0xf
                  else
                    .bCond c8 0xec
              else
                if idx < 44 then
                  if idx < 43 then
                    .addSubImm true true true r31 r3 0x20
                  else
                    .bCond c0 0x140
                else
                  if idx < 45 then
                    .addSubImm true true true r31 r9 0x7
                  else
                    .bCond c8 0x204
            else
              if idx < 49 then
                if idx < 47 then
                  .addSubImm true true true r31 r9 0x3
                else
                  if idx < 48 then
                    .bCond c8 0x334
                  else
                    .ldrUImm .b8 r10 r1 0x20
              else
                if idx < 51 then
                  if idx < 50 then
                    .addSubImm true true true r31 r9 0x1
                  else
                    .bCond c9 0x1a0
                else
                  if idx < 52 then
                    .ldrUImm .b8 r9 r1 0x21
                  else
                    .logicReg false .orrOp .lsl false r9 r10 r9 8
      else
        if idx < 79 then
          if idx < 66 then
            if idx < 59 then
              if idx < 56 then
                if idx < 54 then
                  .crc32c .h16 r8 r8 r9
                else
                  if idx < 55 then
                    .addSubImm true true true r31 r3 0x22
                  else
                    .bCond c8 0x2e0
              else
                if idx < 57 then
                  .b 0x10c
                else
                  if idx < 58 then
                    .ldpGP true .signedOffset r9 r10 r1 0x18
                  else
                    .crc32c .x64 r8 r8 r9
            else
              if idx < 62 then
                if idx < 60 then
                  .crc32c .x64 r8 r8 r10
                else
                  if idx < 61 then
                    .addSubImm true true true r9 r3 0x10
                  else
                    .bCond c0 0xf8
              else
                if idx < 64 then
                  if idx < 63 then
                    .addSubImm true true true r31 r9 0x7
                  else
                    .bCond c8 0x124
                else
                  if idx < 65 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x1e0
          else
            if idx < 72 then
              if idx < 69 then
                if idx < 67 then
                  .ldrUImm .b8 r10 r1 0x28
                else
                  if idx < 68 then
                    .addSubImm true true true r31 r9 0x1
                  else
                    .bCond c9 0x158
              else
                if idx < 70 then
                  .ldrUImm .b8 r9 r1 0x29
                else
                  if idx < 71 then
                    .logicReg false .orrOp .lsl false r9 r10 r9 8
                  else
                    .crc32c .h16 r8 r8 r9
            else
              if idx < 75 then
                if idx < 73 then
                  .addSubImm true true true r31 r3 0x12
                else
                  if idx < 74 then
                    .bCond c9 0xc8
                  else
                    .b 0x46c
              else
                if idx < 77 then
                  if idx < 76 then
                    .ldpGP true .signedOffset r9 r10 r1 0x20
                  else
                    .crc32c .x64 r8 r8 r9
                else
                  if idx < 78 then
                    .crc32c .x64 r8 r8 r10
                  else
                    .ldpGP true .signedOffset r9 r10 r1 0x30
        else
          if idx < 92 then
            if idx < 85 then
              if idx < 82 then
                if idx < 80 then
                  .crc32c .x64 r8 r8 r9
                else
                  if idx < 81 then
                    .crc32c .x64 r8 r8 r10
                  else
                    .addSubImm true true false r9 r3 0x40
              else
                if idx < 83 then
                  .addSubImm true true true r31 r9 0xf
                else
                  if idx < 84 then
                    .bCond c8 0x8c
                  else
                    .addSubImm true true true r31 r3 0x40
            else
              if idx < 88 then
                if idx < 86 then
                  .bCond c0 0x98
                else
                  if idx < 87 then
                    .addSubImm true true true r31 r9 0x7
                  else
                    .bCond c8 0x1ac
              else
                if idx < 90 then
                  if idx < 89 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x2b4
                else
                  if idx < 91 then
                    .ldrUImm .b8 r10 r1 0x40
                  else
                    .addSubImm true true true r31 r9 0x1
          else
            if idx < 99 then
              if idx < 95 then
                if idx < 93 then
                  .bCond c9 0xf8
                else
                  if idx < 94 then
                    .ldrUImm .b8 r9 r1 0x41
                  else
                    .logicReg false .orrOp .lsl false r9 r10 r9 8
              else
                if idx < 97 then
                  if idx < 96 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x42
                else
                  if idx < 98 then
                    .bCond c9 0x68
                  else
                    .ldrUImm .b8 r9 r1 0x42
            else
              if idx < 102 then
                if idx < 100 then
                  .b 0x514
                else
                  if idx < 101 then
                    .ldpGP true .signedOffset r9 r10 r1 0x20
                  else
                    .crc32c .x64 r8 r8 r9
              else
                if idx < 104 then
                  if idx < 103 then
                    .crc32c .x64 r8 r8 r10
                  else
                    .addSubImm true true true r9 r3 0x30
                else
                  if idx < 105 then
                    .bCond c9 0x4c
                  else
                    .addSubImm true true true r31 r9 0x7
    else
      if idx < 159 then
        if idx < 132 then
          if idx < 119 then
            if idx < 112 then
              if idx < 109 then
                if idx < 107 then
                  .bCond c8 0x18c
                else
                  if idx < 108 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x290
              else
                if idx < 110 then
                  .ldrUImm .b8 r10 r1 0x30
                else
                  if idx < 111 then
                    .addSubImm true true true r31 r9 0x1
                  else
                    .bCond c9 0xac
            else
              if idx < 115 then
                if idx < 113 then
                  .ldrUImm .b8 r9 r1 0x31
                else
                  if idx < 114 then
                    .logicReg false .orrOp .lsl false r9 r10 r9 8
                  else
                    .crc32c .h16 r8 r8 r9
              else
                if idx < 117 then
                  if idx < 116 then
                    .addSubImm true true true r31 r3 0x32
                  else
                    .bCond c8 0x2a8
                else
                  if idx < 118 then
                    .b 0x18
                  else
                    .ldpGP true .signedOffset r9 r10 r1 0x40
          else
            if idx < 125 then
              if idx < 122 then
                if idx < 120 then
                  .crc32c .x64 r8 r8 r9
                else
                  if idx < 121 then
                    .crc32c .x64 r8 r8 r10
                  else
                    .addSubImm true true true r9 r3 0x50
              else
                if idx < 123 then
                  .bCond c8 0x64
                else
                  if idx < 124 then
                    .logicReg false .orrOp .lsl true r0 r31 r8 0
                  else
                    .ret r30
            else
              if idx < 128 then
                if idx < 126 then
                  .ldrUImm .x64 r9 r1 0x18
                else
                  if idx < 127 then
                    .crc32c .x64 r8 r8 r9
                  else
                    .addSubImm true true false r9 r3 0x8
              else
                if idx < 130 then
                  if idx < 129 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x94
                else
                  if idx < 131 then
                    .addSubImm true true true r31 r9 0x1
                  else
                    .bCond c8 0x1a0
        else
          if idx < 145 then
            if idx < 138 then
              if idx < 135 then
                if idx < 133 then
                  .addSubImm true true true r31 r3 0x8
                else
                  if idx < 134 then
                    .bCond c0 0xffffffffffffffd8
                  else
                    .ldrUImm .b8 r9 r1 0x20
              else
                if idx < 136 then
                  .b 0x484
                else
                  if idx < 137 then
                    .ldrUImm .x64 r9 r1 0x28
                  else
                    .crc32c .x64 r8 r8 r9
            else
              if idx < 141 then
                if idx < 139 then
                  .addSubImm true true false r9 r3 0x18
                else
                  if idx < 140 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x130
              else
                if idx < 143 then
                  if idx < 142 then
                    .addSubImm true true true r31 r9 0x1
                  else
                    .bCond c8 0x230
                else
                  if idx < 144 then
                    .addSubImm true true true r31 r3 0x18
                  else
                    .bCond c9 0xffffffffffffffac
          else
            if idx < 152 then
              if idx < 148 then
                if idx < 146 then
                  .ldrUImm .b8 r9 r1 0x30
                else
                  if idx < 147 then
                    .b 0x458
                  else
                    .addSubImm true true true r31 r9 0x7
              else
                if idx < 150 then
                  if idx < 149 then
                    .bCond c8 0x130
                  else
                    .addSubImm true true true r31 r9 0x3
                else
                  if idx < 151 then
                    .bCond c8 0x228
                  else
                    .ldrUImm .b8 r10 r1 0x50
            else
              if idx < 155 then
                if idx < 153 then
                  .addSubImm true true true r31 r9 0x1
                else
                  if idx < 154 then
                    .bCond c8 0x304
                  else
                    .crc32c .b8 r8 r8 r10
              else
                if idx < 157 then
                  if idx < 156 then
                    .logicReg false .orrOp .lsl true r0 r31 r8 0
                  else
                    .ret r30
                else
                  if idx < 158 then
                    .ldrUImm .w32 r9 r1 0x18
                  else
                    .crc32c .w32 r8 r8 r9
      else
        if idx < 186 then
          if idx < 172 then
            if idx < 165 then
              if idx < 162 then
                if idx < 160 then
                  .logicImm true .andOp r9 r3 0x6
                else
                  if idx < 161 then
                    .addSubImm true true true r31 r9 0x4
                  else
                    .bCond c1 0x140
              else
                if idx < 163 then
                  .addSubImm true true true r31 r3 0x4
                else
                  if idx < 164 then
                    .bCond c0 0xffffffffffffff60
                  else
                    .ldrUImm .b8 r9 r1 0x1c
            else
              if idx < 168 then
                if idx < 166 then
                  .b 0x40c
                else
                  if idx < 167 then
                    .ldrUImm .w32 r9 r1 0x20
                  else
                    .crc32c .w32 r8 r8 r9
              else
                if idx < 170 then
                  if idx < 169 then
                    .logicImm true .andOp r9 r3 0xe
                  else
                    .addSubImm true true true r31 r9 0xc
                else
                  if idx < 171 then
                    .bCond c1 0x134
                  else
                    .addSubImm true true true r31 r3 0xc
          else
            if idx < 179 then
              if idx < 175 then
                if idx < 173 then
                  .bCond c9 0xffffffffffffff3c
                else
                  if idx < 174 then
                    .b 0x15c
                  else
                    .ldrUImm .x64 r9 r1 0x20
              else
                if idx < 177 then
                  if idx < 176 then
                    .crc32c .x64 r8 r8 r9
                  else
                    .addSubImm true true false r9 r3 0x28
                else
                  if idx < 178 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x1e0
            else
              if idx < 182 then
                if idx < 180 then
                  .addSubImm true true true r31 r9 0x1
                else
                  if idx < 181 then
                    .bCond c8 0x2b4
                  else
                    .addSubImm true true true r31 r3 0x28
              else
                if idx < 184 then
                  if idx < 183 then
                    .bCond c9 0xffffffffffffff14
                  else
                    .ldrUImm .b8 r9 r1 0x28
                else
                  if idx < 185 then
                    .b 0x3c0
                  else
                    .ldrUImm .w32 r9 r1 0x28
        else
          if idx < 199 then
            if idx < 192 then
              if idx < 189 then
                if idx < 187 then
                  .crc32c .w32 r8 r8 r9
                else
                  if idx < 188 then
                    .movWide false .movz r9 0x16 0
                  else
                    .logicReg true .andOp .lsl false r9 r3 r9 0
              else
                if idx < 190 then
                  .addSubImm true true true r31 r9 0x14
                else
                  if idx < 191 then
                    .bCond c1 0x1d8
                  else
                    .addSubImm true true true r31 r3 0x14
            else
              if idx < 195 then
                if idx < 193 then
                  .bCond c9 0xfffffffffffffeec
                else
                  if idx < 194 then
                    .b 0x1c4
                  else
                    .ldrUImm .x64 r9 r1 0x40
              else
                if idx < 197 then
                  if idx < 196 then
                    .crc32c .x64 r8 r8 r9
                  else
                    .addSubImm true true false r9 r3 0x48
                else
                  if idx < 198 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x1cc
          else
            if idx < 206 then
              if idx < 202 then
                if idx < 200 then
                  .addSubImm true true true r31 r9 0x1
                else
                  if idx < 201 then
                    .bCond c8 0x27c
                  else
                    .addSubImm true true true r31 r3 0x48
              else
                if idx < 204 then
                  if idx < 203 then
                    .bCond c9 0xfffffffffffffec4
                  else
                    .ldrUImm .b8 r9 r1 0x48
                else
                  if idx < 205 then
                    .b 0x370
                  else
                    .ldrUImm .x64 r9 r1 0x30
            else
              if idx < 209 then
                if idx < 207 then
                  .crc32c .x64 r8 r8 r9
                else
                  if idx < 208 then
                    .addSubImm true true false r9 r3 0x38
                  else
                    .addSubImm true true true r31 r9 0x3
              else
                if idx < 211 then
                  if idx < 210 then
                    .bCond c8 0x1c8
                  else
                    .addSubImm true true true r31 r9 0x1
                else
                  if idx < 212 then
                    .bCond c8 0x268
                  else
                    .addSubImm true true true r31 r3 0x38
  else
    if idx < 320 then
      if idx < 266 then
        if idx < 239 then
          if idx < 226 then
            if idx < 219 then
              if idx < 216 then
                if idx < 214 then
                  .bCond c9 0xfffffffffffffe98
                else
                  if idx < 215 then
                    .ldrUImm .b8 r9 r1 0x38
                  else
                    .b 0x344
              else
                if idx < 217 then
                  .ldrUImm .w32 r9 r1 0x30
                else
                  if idx < 218 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .logicImm true .andOp r9 r3 0x1e
            else
              if idx < 222 then
                if idx < 220 then
                  .addSubImm true true true r31 r9 0x1c
                else
                  if idx < 221 then
                    .bCond c1 0x1c0
                  else
                    .addSubImm true true true r31 r3 0x1c
              else
                if idx < 224 then
                  if idx < 223 then
                    .bCond c9 0xfffffffffffffe74
                  else
                    .b 0xe4
                else
                  if idx < 225 then
                    .ldrUImm .x64 r9 r1 0x50
                  else
                    .crc32c .x64 r8 r8 r9
          else
            if idx < 232 then
              if idx < 229 then
                if idx < 227 then
                  .addSubImm true true false r9 r3 0x58
                else
                  if idx < 228 then
                    .addSubImm true true true r31 r9 0x3
                  else
                    .bCond c8 0x1b4
              else
                if idx < 230 then
                  .addSubImm true true true r31 r9 0x1
                else
                  if idx < 231 then
                    .bCond c8 0x234
                  else
                    .addSubImm true true true r31 r3 0x58
            else
              if idx < 235 then
                if idx < 233 then
                  .bCond c9 0xfffffffffffffe4c
                else
                  if idx < 234 then
                    .ldrUImm .b8 r9 r1 0x58
                  else
                    .b 0x2f8
              else
                if idx < 237 then
                  if idx < 236 then
                    .ldrUImm .h16 r9 r1 0x20
                  else
                    .crc32c .h16 r8 r8 r9
                else
                  if idx < 238 then
                    .addSubImm true true true r31 r3 0xa
                  else
                    .bCond c9 0xfffffffffffffe34
        else
          if idx < 252 then
            if idx < 245 then
              if idx < 242 then
                if idx < 240 then
                  .ldrUImm .b8 r9 r1 0x22
                else
                  if idx < 241 then
                    .b 0x2e0
                  else
                    .ldrUImm .h16 r9 r1 0x1c
              else
                if idx < 243 then
                  .crc32c .h16 r8 r8 r9
                else
                  if idx < 244 then
                    .addSubImm true true true r31 r3 0x7
                  else
                    .bCond c1 0xfffffffffffffe1c
            else
              if idx < 248 then
                if idx < 246 then
                  .ldrUImm .b8 r9 r1 0x1e
                else
                  if idx < 247 then
                    .b 0x2c8
                  else
                    .ldrUImm .h16 r9 r1 0x24
              else
                if idx < 250 then
                  if idx < 249 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0xf
                else
                  if idx < 251 then
                    .bCond c1 0xfffffffffffffe04
                  else
                    .b 0x208
          else
            if idx < 259 then
              if idx < 255 then
                if idx < 253 then
                  .ldrUImm .w32 r9 r1 0x20
                else
                  if idx < 254 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .movWide false .movz r9 0x26 0
              else
                if idx < 257 then
                  if idx < 256 then
                    .logicReg true .andOp .lsl false r9 r3 r9 0
                  else
                    .addSubImm true true true r31 r9 0x24
                else
                  if idx < 258 then
                    .bCond c1 0x1e0
                  else
                    .addSubImm true true true r31 r3 0x24
            else
              if idx < 262 then
                if idx < 260 then
                  .bCond c9 0xfffffffffffffde0
                else
                  if idx < 261 then
                    .ldrUImm .b8 r9 r1 0x24
                  else
                    .b 0x28c
              else
                if idx < 264 then
                  if idx < 263 then
                    .ldrUImm .w32 r9 r1 0x40
                  else
                    .crc32c .w32 r8 r8 r9
                else
                  if idx < 265 then
                    .movWide false .movz r9 0x46 0
                  else
                    .logicReg true .andOp .lsl false r9 r3 r9 0
      else
        if idx < 293 then
          if idx < 279 then
            if idx < 272 then
              if idx < 269 then
                if idx < 267 then
                  .addSubImm true true true r31 r9 0x44
                else
                  if idx < 268 then
                    .bCond c1 0x1d0
                  else
                    .addSubImm true true true r31 r3 0x44
              else
                if idx < 270 then
                  .bCond c9 0xfffffffffffffdb8
                else
                  if idx < 271 then
                    .ldrUImm .b8 r9 r1 0x44
                  else
                    .b 0x264
            else
              if idx < 275 then
                if idx < 273 then
                  .ldrUImm .w32 r9 r1 0x30
                else
                  if idx < 274 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .movWide false .movz r9 0x36 0
              else
                if idx < 277 then
                  if idx < 276 then
                    .logicReg true .andOp .lsl false r9 r3 r9 0
                  else
                    .addSubImm true true true r31 r9 0x34
                else
                  if idx < 278 then
                    .bCond c1 0x1c0
                  else
                    .addSubImm true true true r31 r3 0x34
          else
            if idx < 286 then
              if idx < 282 then
                if idx < 280 then
                  .bCond c9 0xfffffffffffffd90
                else
                  if idx < 281 then
                    .ldrUImm .b8 r9 r1 0x34
                  else
                    .b 0x23c
              else
                if idx < 284 then
                  if idx < 283 then
                    .ldrUImm .h16 r9 r1 0x30
                  else
                    .crc32c .h16 r8 r8 r9
                else
                  if idx < 285 then
                    .addSubImm true true true r31 r3 0x1a
                  else
                    .bCond c9 0xfffffffffffffd78
            else
              if idx < 289 then
                if idx < 287 then
                  .ldrUImm .b8 r9 r1 0x32
                else
                  if idx < 288 then
                    .b 0x224
                  else
                    .ldrUImm .w32 r9 r1 0x50
              else
                if idx < 291 then
                  if idx < 290 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .movWide false .movz r9 0x56 0
                else
                  if idx < 292 then
                    .logicReg true .andOp .lsl false r9 r3 r9 0
                  else
                    .addSubImm true true true r31 r9 0x54
        else
          if idx < 306 then
            if idx < 299 then
              if idx < 296 then
                if idx < 294 then
                  .bCond c1 0x198
                else
                  if idx < 295 then
                    .addSubImm true true true r31 r3 0x54
                  else
                    .bCond c9 0xfffffffffffffd50
              else
                if idx < 297 then
                  .ldrUImm .b8 r9 r1 0x54
                else
                  if idx < 298 then
                    .b 0x1fc
                  else
                    .ldrUImm .w32 r9 r1 0x28
            else
              if idx < 302 then
                if idx < 300 then
                  .crc32c .w32 r8 r8 r9
                else
                  if idx < 301 then
                    .movWide false .movz r9 0x2e 0
                  else
                    .logicReg true .andOp .lsl false r9 r3 r9 0
              else
                if idx < 304 then
                  if idx < 303 then
                    .addSubImm true true true r31 r9 0x2c
                  else
                    .bCond c1 0x188
                else
                  if idx < 305 then
                    .addSubImm true true true r31 r3 0x2c
                  else
                    .bCond c9 0xfffffffffffffd28
          else
            if idx < 313 then
              if idx < 309 then
                if idx < 307 then
                  .ldrUImm .b8 r9 r1 0x2c
                else
                  if idx < 308 then
                    .b 0x1d4
                  else
                    .ldrUImm .h16 r9 r1 0x2c
              else
                if idx < 311 then
                  if idx < 310 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x16
                else
                  if idx < 312 then
                    .bCond c9 0xfffffffffffffd10
                  else
                    .b 0x174
            else
              if idx < 316 then
                if idx < 314 then
                  .ldrUImm .w32 r9 r1 0x48
                else
                  if idx < 315 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .movWide false .movz r9 0x4e 0
              else
                if idx < 318 then
                  if idx < 317 then
                    .logicReg true .andOp .lsl false r9 r3 r9 0
                  else
                    .addSubImm true true true r31 r9 0x4c
                else
                  if idx < 319 then
                    .bCond c1 0x164
                  else
                    .addSubImm true true true r31 r3 0x4c
    else
      if idx < 373 then
        if idx < 346 then
          if idx < 333 then
            if idx < 326 then
              if idx < 323 then
                if idx < 321 then
                  .bCond c9 0xfffffffffffffcec
                else
                  if idx < 322 then
                    .ldrUImm .b8 r9 r1 0x4c
                  else
                    .b 0x198
              else
                if idx < 324 then
                  .ldrUImm .w32 r9 r1 0x38
                else
                  if idx < 325 then
                    .crc32c .w32 r8 r8 r9
                  else
                    .logicImm true .andOp r9 r3 0x3e
            else
              if idx < 329 then
                if idx < 327 then
                  .addSubImm true true true r31 r9 0x3c
                else
                  if idx < 328 then
                    .bCond c1 0x158
                  else
                    .addSubImm true true true r31 r3 0x3c
              else
                if idx < 331 then
                  if idx < 330 then
                    .bCond c9 0xfffffffffffffcc8
                  else
                    .ldrUImm .b8 r9 r1 0x3c
                else
                  if idx < 332 then
                    .b 0x174
                  else
                    .ldrUImm .h16 r9 r1 0x34
          else
            if idx < 339 then
              if idx < 336 then
                if idx < 334 then
                  .crc32c .h16 r8 r8 r9
                else
                  if idx < 335 then
                    .addSubImm true true true r31 r3 0x1f
                  else
                    .bCond c1 0xfffffffffffffcb0
              else
                if idx < 337 then
                  .b 0xe4
                else
                  if idx < 338 then
                    .ldrUImm .w32 r9 r1 0x58
                  else
                    .crc32c .w32 r8 r8 r9
            else
              if idx < 342 then
                if idx < 340 then
                  .logicImm true .andOp r9 r3 0x7e
                else
                  if idx < 341 then
                    .addSubImm true true true r31 r9 0x5c
                  else
                    .bCond c1 0x138
              else
                if idx < 344 then
                  if idx < 343 then
                    .addSubImm true true true r31 r3 0x5c
                  else
                    .bCond c9 0xfffffffffffffc90
                else
                  if idx < 345 then
                    .ldrUImm .b8 r9 r1 0x5c
                  else
                    .b 0x13c
        else
          if idx < 359 then
            if idx < 352 then
              if idx < 349 then
                if idx < 347 then
                  .ldrUImm .b8 r9 r1 0x51
                else
                  if idx < 348 then
                    .logicReg false .orrOp .lsl false r9 r10 r9 8
                  else
                    .crc32c .h16 r8 r8 r9
              else
                if idx < 350 then
                  .addSubImm true true true r31 r3 0x52
                else
                  if idx < 351 then
                    .bCond c9 0xfffffffffffffc74
                  else
                    .ldrUImm .b8 r9 r1 0x52
            else
              if idx < 355 then
                if idx < 353 then
                  .b 0x120
                else
                  if idx < 354 then
                    .ldrUImm .h16 r9 r1 0x28
                  else
                    .crc32c .h16 r8 r8 r9
              else
                if idx < 357 then
                  if idx < 356 then
                    .addSubImm true true true r31 r3 0x2a
                  else
                    .bCond c9 0xfffffffffffffc5c
                else
                  if idx < 358 then
                    .ldrUImm .b8 r9 r1 0x2a
                  else
                    .b 0x108
          else
            if idx < 366 then
              if idx < 362 then
                if idx < 360 then
                  .ldrUImm .h16 r9 r1 0x48
                else
                  if idx < 361 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x4a
              else
                if idx < 364 then
                  if idx < 363 then
                    .bCond c9 0xfffffffffffffc44
                  else
                    .ldrUImm .b8 r9 r1 0x4a
                else
                  if idx < 365 then
                    .b 0xf0
                  else
                    .ldrUImm .h16 r9 r1 0x38
            else
              if idx < 369 then
                if idx < 367 then
                  .crc32c .h16 r8 r8 r9
                else
                  if idx < 368 then
                    .addSubImm true true true r31 r3 0x3a
                  else
                    .bCond c9 0xfffffffffffffc2c
              else
                if idx < 371 then
                  if idx < 370 then
                    .ldrUImm .b8 r9 r1 0x3a
                  else
                    .b 0xd8
                else
                  if idx < 372 then
                    .ldrUImm .h16 r9 r1 0x58
                  else
                    .crc32c .h16 r8 r8 r9
      else
        if idx < 400 then
          if idx < 386 then
            if idx < 379 then
              if idx < 376 then
                if idx < 374 then
                  .addSubImm true true true r31 r3 0x5a
                else
                  if idx < 375 then
                    .bCond c9 0xfffffffffffffc14
                  else
                    .ldrUImm .b8 r9 r1 0x5a
              else
                if idx < 377 then
                  .b 0xc0
                else
                  if idx < 378 then
                    .ldrUImm .h16 r9 r1 0x24
                  else
                    .crc32c .h16 r8 r8 r9
            else
              if idx < 382 then
                if idx < 380 then
                  .addSubImm true true true r31 r3 0x26
                else
                  if idx < 381 then
                    .bCond c9 0xfffffffffffffbfc
                  else
                    .ldrUImm .b8 r9 r1 0x26
              else
                if idx < 384 then
                  if idx < 383 then
                    .b 0xa8
                  else
                    .ldrUImm .h16 r9 r1 0x44
                else
                  if idx < 385 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x46
          else
            if idx < 393 then
              if idx < 389 then
                if idx < 387 then
                  .bCond c9 0xfffffffffffffbe4
                else
                  if idx < 388 then
                    .ldrUImm .b8 r9 r1 0x46
                  else
                    .b 0x90
              else
                if idx < 391 then
                  if idx < 390 then
                    .ldrUImm .h16 r9 r1 0x34
                  else
                    .crc32c .h16 r8 r8 r9
                else
                  if idx < 392 then
                    .addSubImm true true true r31 r3 0x36
                  else
                    .bCond c9 0xfffffffffffffbcc
            else
              if idx < 396 then
                if idx < 394 then
                  .ldrUImm .b8 r9 r1 0x36
                else
                  if idx < 395 then
                    .b 0x78
                  else
                    .ldrUImm .h16 r9 r1 0x54
              else
                if idx < 398 then
                  if idx < 397 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x56
                else
                  if idx < 399 then
                    .bCond c9 0xfffffffffffffbb4
                  else
                    .ldrUImm .b8 r9 r1 0x56
        else
          if idx < 413 then
            if idx < 406 then
              if idx < 403 then
                if idx < 401 then
                  .b 0x60
                else
                  if idx < 402 then
                    .ldrUImm .h16 r9 r1 0x2c
                  else
                    .crc32c .h16 r8 r8 r9
              else
                if idx < 404 then
                  .addSubImm true true true r31 r3 0x2e
                else
                  if idx < 405 then
                    .bCond c9 0xfffffffffffffb9c
                  else
                    .ldrUImm .b8 r9 r1 0x2e
            else
              if idx < 409 then
                if idx < 407 then
                  .b 0x48
                else
                  if idx < 408 then
                    .ldrUImm .h16 r9 r1 0x4c
                  else
                    .crc32c .h16 r8 r8 r9
              else
                if idx < 411 then
                  if idx < 410 then
                    .addSubImm true true true r31 r3 0x4e
                  else
                    .bCond c9 0xfffffffffffffb84
                else
                  if idx < 412 then
                    .ldrUImm .b8 r9 r1 0x4e
                  else
                    .b 0x30
          else
            if idx < 420 then
              if idx < 416 then
                if idx < 414 then
                  .ldrUImm .h16 r9 r1 0x3c
                else
                  if idx < 415 then
                    .crc32c .h16 r8 r8 r9
                  else
                    .addSubImm true true true r31 r3 0x3f
              else
                if idx < 418 then
                  if idx < 417 then
                    .bCond c1 0xfffffffffffffb6c
                  else
                    .ldrUImm .b8 r9 r1 0x3e
                else
                  if idx < 419 then
                    .b 0x18
                  else
                    .ldrUImm .h16 r9 r1 0x5c
            else
              if idx < 423 then
                if idx < 421 then
                  .crc32c .h16 r8 r8 r9
                else
                  if idx < 422 then
                    .addSubImm true true true r31 r3 0x5f
                  else
                    .bCond c1 0xfffffffffffffb54
              else
                if idx < 425 then
                  if idx < 424 then
                    .ldrUImm .b8 r9 r1 0x5e
                  else
                    .crc32c .b8 r8 r8 r9
                else
                  if idx < 426 then
                    .logicReg false .orrOp .lsl true r0 r31 r8 0
                  else
                    .ret r30

set_option maxRecDepth 8192 in
private theorem extendHwRaw_decode_ok :
    checkWordsAux extendHwRawWords extendHwRawInsn 427 = true := rfl

private theorem extendHwRaw_decode_cert (idx : Nat) (hsz : idx < extendHwRawWords.size)
    (hlt : idx < 427) :
    Arm64.decode (extendHwRawWords[idx]'hsz) = some (extendHwRawInsn idx) :=
  checkWordsAux_spec extendHwRawWords extendHwRawInsn 427 extendHwRaw_decode_ok idx hsz hlt


/-! ### Full code and global-constant loading predicates -/

/-- All 7 reachable hardware CRC32C functions are loaded in `code` with valid
Mach-O relocations against `L` and `m`. -/
structure CodeLoaded (code : UInt64 → Option UInt32) (m : Arm64.Mem) (L : CodeLayout) : Prop where
  combine3         : FnLoaded code m L L.combine3Base combine3Words combine3Branches combine3Gots
  combine6         : FnLoaded code m L L.combine6Base combine6Words combine6Branches combine6Gots
  hwLoop           : FnLoaded code m L L.hwLoopBase hwLoopWords hwLoopBranches hwLoopGots
  hwFold6Loop      : FnLoaded code m L L.hwFold6LoopBase hwFold6LoopWords hwFold6LoopBranches hwFold6LoopGots
  hwFold6          : FnLoaded code m L L.hwFold6Base hwFold6Words hwFold6Branches hwFold6Gots
  rawExtendHwMulti : FnLoaded code m L L.rawExtendHwMultiBase rawExtendHwMultiWords rawExtendHwMultiBranches rawExtendHwMultiGots
  extendHwRaw      : FnLoaded code m L L.extendHwRawBase extendHwRawWords extendHwRawBranches extendHwRawGots

/-- Initialized module-level CRC32C constants and 2 KiB shift table mapped read-only
in `m` (so any `.rw` stack write preserves them automatically and any rogue write to
constants would fault). -/
structure GlobalsLoaded (m : Arm64.Mem) (L : CodeLayout) : Prop where
  hwOne      : m.hasROU32 L.hwOneAddr Crc32c.hwOne
  hwX64      : m.hasROU32 L.hwX64Addr Crc32c.hwX64
  tblPtr     : m.hasROU64 L.hwShiftSmallAddr L.tblObjAddr
  tblBytes   : m.hasROBytes (L.tblObjAddr + 0x18) Crc32c.hwShiftSmallBytes
  kFold128_1 : m.hasROU64 L.kFold128_1Addr Crc32c.kFold128_1
  kFold128_2 : m.hasROU64 L.kFold128_2Addr Crc32c.kFold128_2
  kFold256_1 : m.hasROU64 L.kFold256_1Addr Crc32c.kFold256_1
  kFold256_2 : m.hasROU64 L.kFold256_2Addr Crc32c.kFold256_2
  kFold384_1 : m.hasROU64 L.kFold384_1Addr Crc32c.kFold384_1
  kFold384_2 : m.hasROU64 L.kFold384_2Addr Crc32c.kFold384_2
  kFold512_1 : m.hasROU64 L.kFold512_1Addr Crc32c.kFold512_1
  kFold512_2 : m.hasROU64 L.kFold512_2Addr Crc32c.kFold512_2

/-! ### Preservation of `CodeLoaded` and `GlobalsLoaded` across `.rw` stack writes -/

theorem FnLoaded.preserves_writeSlot64 {code : UInt64 → Option UInt32} {m : Arm64.Mem}
    {L : CodeLayout} {base : UInt64} {words : Array UInt32}
    {branches : List BranchReloc} {gots : List GotReloc}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len)
    (v : UInt64) (hfn : FnLoaded code m L base words branches gots) :
    FnLoaded code (m.writeSlot64 (lo + off.toUInt64) v) L base words branches gots :=
  ⟨hfn.1, hfn.2.1, fun g hg => (hfn.2.2 g hg).preserves_writeSlot64 hrw off hoff v⟩

theorem FnLoaded.preserves_writeSlot32 {code : UInt64 → Option UInt32} {m : Arm64.Mem}
    {L : CodeLayout} {base : UInt64} {words : Array UInt32}
    {branches : List BranchReloc} {gots : List GotReloc}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len)
    (v : UInt32) (hfn : FnLoaded code m L base words branches gots) :
    FnLoaded code (m.writeSlot32 (lo + off.toUInt64) v) L base words branches gots :=
  ⟨hfn.1, hfn.2.1, fun g hg => (hfn.2.2 g hg).preserves_writeSlot32 hrw off hoff v⟩

theorem CodeLoaded.preserves_writeSlot64 {code : UInt64 → Option UInt32} {m : Arm64.Mem}
    {L : CodeLayout} {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len)
    (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64) (hc : CodeLoaded code m L) :
    CodeLoaded code (m.writeSlot64 (lo + off.toUInt64) v) L where
  combine3         := hc.combine3.preserves_writeSlot64 hrw off hoff v
  combine6         := hc.combine6.preserves_writeSlot64 hrw off hoff v
  hwLoop           := hc.hwLoop.preserves_writeSlot64 hrw off hoff v
  hwFold6Loop      := hc.hwFold6Loop.preserves_writeSlot64 hrw off hoff v
  hwFold6          := hc.hwFold6.preserves_writeSlot64 hrw off hoff v
  rawExtendHwMulti := hc.rawExtendHwMulti.preserves_writeSlot64 hrw off hoff v
  extendHwRaw      := hc.extendHwRaw.preserves_writeSlot64 hrw off hoff v

theorem CodeLoaded.preserves_writeSlot32 {code : UInt64 → Option UInt32} {m : Arm64.Mem}
    {L : CodeLayout} {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len)
    (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32) (hc : CodeLoaded code m L) :
    CodeLoaded code (m.writeSlot32 (lo + off.toUInt64) v) L where
  combine3         := hc.combine3.preserves_writeSlot32 hrw off hoff v
  combine6         := hc.combine6.preserves_writeSlot32 hrw off hoff v
  hwLoop           := hc.hwLoop.preserves_writeSlot32 hrw off hoff v
  hwFold6Loop      := hc.hwFold6Loop.preserves_writeSlot32 hrw off hoff v
  hwFold6          := hc.hwFold6.preserves_writeSlot32 hrw off hoff v
  rawExtendHwMulti := hc.rawExtendHwMulti.preserves_writeSlot32 hrw off hoff v
  extendHwRaw      := hc.extendHwRaw.preserves_writeSlot32 hrw off hoff v

theorem GlobalsLoaded.preserves_writeSlot64 {m : Arm64.Mem} {L : CodeLayout}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len)
    (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64) (hg : GlobalsLoaded m L) :
    GlobalsLoaded (m.writeSlot64 (lo + off.toUInt64) v) L where
  hwOne      := Arm64.Mem.writeSlot64_preserves_hasROU32 hrw off hoff v hg.hwOne
  hwX64      := Arm64.Mem.writeSlot64_preserves_hasROU32 hrw off hoff v hg.hwX64
  tblPtr     := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.tblPtr
  tblBytes   := Arm64.Mem.writeSlot64_preserves_hasROBytes hrw off hoff v hg.tblBytes
  kFold128_1 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold128_1
  kFold128_2 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold128_2
  kFold256_1 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold256_1
  kFold256_2 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold256_2
  kFold384_1 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold384_1
  kFold384_2 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold384_2
  kFold512_1 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold512_1
  kFold512_2 := Arm64.Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hg.kFold512_2

theorem GlobalsLoaded.preserves_writeSlot32 {m : Arm64.Mem} {L : CodeLayout}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len)
    (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32) (hg : GlobalsLoaded m L) :
    GlobalsLoaded (m.writeSlot32 (lo + off.toUInt64) v) L where
  hwOne      := Arm64.Mem.writeSlot32_preserves_hasROU32 hrw off hoff v hg.hwOne
  hwX64      := Arm64.Mem.writeSlot32_preserves_hasROU32 hrw off hoff v hg.hwX64
  tblPtr     := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.tblPtr
  tblBytes   := Arm64.Mem.writeSlot32_preserves_hasROBytes hrw off hoff v hg.tblBytes
  kFold128_1 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold128_1
  kFold128_2 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold128_2
  kFold256_1 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold256_1
  kFold256_2 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold256_2
  kFold384_1 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold384_1
  kFold384_2 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold384_2
  kFold512_1 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold512_1
  kFold512_2 := Arm64.Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hg.kFold512_2

/-! ### Fast O(log N) instruction-fetch & relocation stepping lemmas -/

private theorem u64_add_sub_cancel (a b : UInt64) : a + (b - a) = b := by
  rw [← UInt64.toBitVec_inj]
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem step_branch_call {code : UInt64 → Option UInt32} {s : Arm64.ArmState}
    {calleeBase : UInt64} (hb : BranchAt code s.pc calleeBase true) :
    Arm64.step code s = some { (s.setX r30 (s.pc + 4)) with pc := calleeBase } := by
  rcases hb with ⟨w, hc, hd⟩
  rw [Arm64.step_of_decoded hc hd]
  simp [Arm64.execInstr, r30, u64_add_sub_cancel]

theorem step_branch_jump {code : UInt64 → Option UInt32} {s : Arm64.ArmState}
    {calleeBase : UInt64} (hb : BranchAt code s.pc calleeBase false) :
    Arm64.step code s = some { s with pc := calleeBase } := by
  rcases hb with ⟨w, hc, hd⟩
  rw [Arm64.step_of_decoded hc hd]
  simp [Arm64.execInstr, u64_add_sub_cancel]

theorem step_combine3 {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.combine3Base + (4 * idx).toUInt64)
    (hok : decide (idx < 44 ∧ isRelocIdx combine3Branches combine3Gots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (combine3Insn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < combine3Words.size := by rw [combine3Words_size]; exact hp.1
  have hfetch := hc.combine3.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (combine3_decode_cert idx hsz hp.1)

theorem step_combine6 {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.combine6Base + (4 * idx).toUInt64)
    (hok : decide (idx < 65 ∧ isRelocIdx combine6Branches combine6Gots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (combine6Insn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < combine6Words.size := by rw [combine6Words_size]; exact hp.1
  have hfetch := hc.combine6.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (combine6_decode_cert idx hsz hp.1)

theorem step_hwLoop {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.hwLoopBase + (4 * idx).toUInt64)
    (hok : decide (idx < 99 ∧ isRelocIdx hwLoopBranches hwLoopGots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (hwLoopInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < hwLoopWords.size := by rw [hwLoopWords_size]; exact hp.1
  have hfetch := hc.hwLoop.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (hwLoop_decode_cert idx hsz hp.1)

theorem step_hwFold6Loop {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.hwFold6LoopBase + (4 * idx).toUInt64)
    (hok : decide (idx < 197 ∧ isRelocIdx hwFold6LoopBranches hwFold6LoopGots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (hwFold6LoopInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < hwFold6LoopWords.size := by rw [hwFold6LoopWords_size]; exact hp.1
  have hfetch := hc.hwFold6Loop.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (hwFold6Loop_decode_cert idx hsz hp.1)

theorem step_hwFold6 {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.hwFold6Base + (4 * idx).toUInt64)
    (hok : decide (idx < 186 ∧ isRelocIdx hwFold6Branches hwFold6Gots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (hwFold6Insn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < hwFold6Words.size := by rw [hwFold6Words_size]; exact hp.1
  have hfetch := hc.hwFold6.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (hwFold6_decode_cert idx hsz hp.1)

theorem step_rawExtendHwMulti {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.rawExtendHwMultiBase + (4 * idx).toUInt64)
    (hok : decide (idx < 119 ∧ isRelocIdx rawExtendHwMultiBranches rawExtendHwMultiGots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (rawExtendHwMultiInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < rawExtendHwMultiWords.size := by rw [rawExtendHwMultiWords_size]; exact hp.1
  have hfetch := hc.rawExtendHwMulti.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (rawExtendHwMulti_decode_cert idx hsz hp.1)

theorem step_extendHwRaw {code : UInt64 → Option UInt32} {m : Arm64.Mem} {L : CodeLayout}
    (hc : CodeLoaded code m L) (idx : Nat) (s : Arm64.ArmState)
    (hpc : s.pc = L.extendHwRawBase + (4 * idx).toUInt64)
    (hok : decide (idx < 427 ∧ isRelocIdx extendHwRawBranches extendHwRawGots idx = false) = true := by decide) :
    Arm64.step code s = Arm64.execInstr s (extendHwRawInsn idx) := by
  have hp := of_decide_eq_true hok
  have hsz : idx < extendHwRawWords.size := by rw [extendHwRawWords_size]; exact hp.1
  have hfetch := hc.extendHwRaw.1 idx hsz hp.2
  rw [← hpc] at hfetch
  exact Arm64.step_of_decoded hfetch (extendHwRaw_decode_cert idx hsz hp.1)


end Crc32c.Arm64MC
