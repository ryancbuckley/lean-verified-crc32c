/-
Self-contained AArch64 (A64) binary instruction decoder and operational ISA
semantics for machine-code verification (Phase 7).

Imports only `SimdModels.Models` (Lean core `Init` only, no Mathlib), so native
validation binaries (`asl_check`) compile directly against this module and check
decoded 32-bit A64 opcodes against Arm's machine-readable ASL via ASLp.

Key architectural fidelities:
- General-purpose registers `X0..X30` (`64`-bit), zero register `XZR`/`WZR`
  (register encoding `31` in register-value contexts), and `SP` (register
  encoding `31` in stack/base/non-flag-setting immediate contexts).
- Writing a 32-bit `Wd` register zero-extends bits `[63:32]` of `Xd`.
- SIMD/FP registers `V0..V31` (`128`-bit, where `V31` is a real register, not
  zero); writing a 64-bit `Dd` register or `Vd.8B` vector zero-extends bits
  `[127:64]` of `Vd`, whereas `INS Vd.D[idx], ...` preserves the other lane.
- Condition flags `PSTATE.{N,Z,C,V}` computed via Arm ASL's `AddWithCarry` and
  tested via Arm ASL's `ConditionHolds`.
- Byte-addressed permissioned memory (`Perm.ro` vs `Perm.rw` vs unmapped `none`),
  so out-of-bounds reads, header reads on borrowed slices, or writes to read-only
  input/constant memory fault (`none`).
- `CRC32C{B,H,W,X}` and `PMULL Vd.1Q, Vn.1D, Vm.1D` delegate directly to the
  validated `SimdModels.Model` definitions.
-/
import SimdModels.Models

namespace SimdModels.Arm64

/-- `PSTATE.{N, Z, C, V}` condition flags. -/
structure PState where
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Arm ASL `AddWithCarry(bits(N) x, bits(N) y, bit carry_in)`. -/
def addWithCarry {w : Nat} (x y : BitVec w) (cin : Bool) : BitVec w × PState :=
  let cNat : Nat := if cin then 1 else 0
  let usum : Nat := x.toNat + y.toNat + cNat
  let ssum : Int := x.toInt + y.toInt + Int.ofNat cNat
  let res : BitVec w := BitVec.ofNat w usum
  let n : Bool := res.msb
  let z : Bool := res == 0
  let c : Bool := decide (res.toNat != usum)
  let v : Bool := decide (res.toInt != ssum)
  (res, { n, z, c, v })

/-- Arm ASL `ConditionHolds(bits(4) cond)`. -/
def conditionHolds (cond : Fin 16) (p : PState) : Bool :=
  let base :=
    match cond.val >>> 1 with
    | 0 => p.z
    | 1 => p.c
    | 2 => p.n
    | 3 => p.v
    | 4 => p.c && !p.z
    | 5 => p.n == p.v
    | 6 => (p.n == p.v) && !p.z
    | _ => true
  if (cond.val &&& 1) == 1 && cond.val != 15 then !base else base

/-- 5-bit register specifier (`0..31`). -/
abbrev RegIdx := Fin 32

/-- General-purpose registers `X0..X30` as a flat structure so symbolic state
updates reduce in O(1) without growing nested `if` chains. -/
structure RegFile where
  x0  : UInt64 := 0
  x1  : UInt64 := 0
  x2  : UInt64 := 0
  x3  : UInt64 := 0
  x4  : UInt64 := 0
  x5  : UInt64 := 0
  x6  : UInt64 := 0
  x7  : UInt64 := 0
  x8  : UInt64 := 0
  x9  : UInt64 := 0
  x10 : UInt64 := 0
  x11 : UInt64 := 0
  x12 : UInt64 := 0
  x13 : UInt64 := 0
  x14 : UInt64 := 0
  x15 : UInt64 := 0
  x16 : UInt64 := 0
  x17 : UInt64 := 0
  x18 : UInt64 := 0
  x19 : UInt64 := 0
  x20 : UInt64 := 0
  x21 : UInt64 := 0
  x22 : UInt64 := 0
  x23 : UInt64 := 0
  x24 : UInt64 := 0
  x25 : UInt64 := 0
  x26 : UInt64 := 0
  x27 : UInt64 := 0
  x28 : UInt64 := 0
  x29 : UInt64 := 0
  x30 : UInt64 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Read `Xn`, with `31` reading `XZR = 0`. -/
def RegFile.get (r : RegFile) (i : RegIdx) : UInt64 :=
  match i.val with
  | 0  => r.x0  | 1  => r.x1  | 2  => r.x2  | 3  => r.x3
  | 4  => r.x4  | 5  => r.x5  | 6  => r.x6  | 7  => r.x7
  | 8  => r.x8  | 9  => r.x9  | 10 => r.x10 | 11 => r.x11
  | 12 => r.x12 | 13 => r.x13 | 14 => r.x14 | 15 => r.x15
  | 16 => r.x16 | 17 => r.x17 | 18 => r.x18 | 19 => r.x19
  | 20 => r.x20 | 21 => r.x21 | 22 => r.x22 | 23 => r.x23
  | 24 => r.x24 | 25 => r.x25 | 26 => r.x26 | 27 => r.x27
  | 28 => r.x28 | 29 => r.x29 | 30 => r.x30 | _  => 0

/-- Write `Xn`, discarding writes to `31` (`XZR`). -/
def RegFile.set (r : RegFile) (i : RegIdx) (v : UInt64) : RegFile :=
  match i.val with
  | 0  => { r with x0  := v } | 1  => { r with x1  := v }
  | 2  => { r with x2  := v } | 3  => { r with x3  := v }
  | 4  => { r with x4  := v } | 5  => { r with x5  := v }
  | 6  => { r with x6  := v } | 7  => { r with x7  := v }
  | 8  => { r with x8  := v } | 9  => { r with x9  := v }
  | 10 => { r with x10 := v } | 11 => { r with x11 := v }
  | 12 => { r with x12 := v } | 13 => { r with x13 := v }
  | 14 => { r with x14 := v } | 15 => { r with x15 := v }
  | 16 => { r with x16 := v } | 17 => { r with x17 := v }
  | 18 => { r with x18 := v } | 19 => { r with x19 := v }
  | 20 => { r with x20 := v } | 21 => { r with x21 := v }
  | 22 => { r with x22 := v } | 23 => { r with x23 := v }
  | 24 => { r with x24 := v } | 25 => { r with x25 := v }
  | 26 => { r with x26 := v } | 27 => { r with x27 := v }
  | 28 => { r with x28 := v } | 29 => { r with x29 := v }
  | 30 => { r with x30 := v } | _  => r

/-- 128-bit SIMD/FP registers `V0..V31` (`V31` is a real register). -/
structure SimdFile where
  v0  : V128 := 0
  v1  : V128 := 0
  v2  : V128 := 0
  v3  : V128 := 0
  v4  : V128 := 0
  v5  : V128 := 0
  v6  : V128 := 0
  v7  : V128 := 0
  v8  : V128 := 0
  v9  : V128 := 0
  v10 : V128 := 0
  v11 : V128 := 0
  v12 : V128 := 0
  v13 : V128 := 0
  v14 : V128 := 0
  v15 : V128 := 0
  v16 : V128 := 0
  v17 : V128 := 0
  v18 : V128 := 0
  v19 : V128 := 0
  v20 : V128 := 0
  v21 : V128 := 0
  v22 : V128 := 0
  v23 : V128 := 0
  v24 : V128 := 0
  v25 : V128 := 0
  v26 : V128 := 0
  v27 : V128 := 0
  v28 : V128 := 0
  v29 : V128 := 0
  v30 : V128 := 0
  v31 : V128 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Read 128-bit vector register `Vn` (`0..31`). -/
def SimdFile.get (r : SimdFile) (i : RegIdx) : V128 :=
  match i.val with
  | 0  => r.v0  | 1  => r.v1  | 2  => r.v2  | 3  => r.v3
  | 4  => r.v4  | 5  => r.v5  | 6  => r.v6  | 7  => r.v7
  | 8  => r.v8  | 9  => r.v9  | 10 => r.v10 | 11 => r.v11
  | 12 => r.v12 | 13 => r.v13 | 14 => r.v14 | 15 => r.v15
  | 16 => r.v16 | 17 => r.v17 | 18 => r.v18 | 19 => r.v19
  | 20 => r.v20 | 21 => r.v21 | 22 => r.v22 | 23 => r.v23
  | 24 => r.v24 | 25 => r.v25 | 26 => r.v26 | 27 => r.v27
  | 28 => r.v28 | 29 => r.v29 | 30 => r.v30 | _  => r.v31

/-- Write 128-bit vector register `Vn` (`0..31`). -/
def SimdFile.set (r : SimdFile) (i : RegIdx) (v : V128) : SimdFile :=
  match i.val with
  | 0  => { r with v0  := v } | 1  => { r with v1  := v }
  | 2  => { r with v2  := v } | 3  => { r with v3  := v }
  | 4  => { r with v4  := v } | 5  => { r with v5  := v }
  | 6  => { r with v6  := v } | 7  => { r with v7  := v }
  | 8  => { r with v8  := v } | 9  => { r with v9  := v }
  | 10 => { r with v10 := v } | 11 => { r with v11 := v }
  | 12 => { r with v12 := v } | 13 => { r with v13 := v }
  | 14 => { r with v14 := v } | 15 => { r with v15 := v }
  | 16 => { r with v16 := v } | 17 => { r with v17 := v }
  | 18 => { r with v18 := v } | 19 => { r with v19 := v }
  | 20 => { r with v20 := v } | 21 => { r with v21 := v }
  | 22 => { r with v22 := v } | 23 => { r with v23 := v }
  | 24 => { r with v24 := v } | 25 => { r with v25 := v }
  | 26 => { r with v26 := v } | 27 => { r with v27 := v }
  | 28 => { r with v28 := v } | 29 => { r with v29 := v }
  | 30 => { r with v30 := v } | _  => { r with v31 := v }

/-- Per-byte memory access permission (`ro` for input buffers and constant
tables/GOT, `rw` for writable stack frames). Unmapped addresses are `none`. -/
inductive Perm where
  | ro
  | rw
  deriving DecidableEq, Repr, Inhabited

/-- Byte-addressed partial memory with read/write permissions. -/
abbrev Mem := UInt64 → Option (Perm × UInt8)

namespace Mem

def readU8 (m : Mem) (addr : UInt64) : Option UInt8 :=
  match m addr with
  | some (_, b) => some b
  | none => none

def readU16LE (m : Mem) (addr : UInt64) : Option UInt16 := do
  let b0 ← m.readU8 addr
  let b1 ← m.readU8 (addr + 1)
  some (b0.toUInt16 ||| (b1.toUInt16 <<< 8))

def readU32LE (m : Mem) (addr : UInt64) : Option UInt32 := do
  let b0 ← m.readU8 addr
  let b1 ← m.readU8 (addr + 1)
  let b2 ← m.readU8 (addr + 2)
  let b3 ← m.readU8 (addr + 3)
  some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

def readU64LE (m : Mem) (addr : UInt64) : Option UInt64 := do
  let b0 ← m.readU8 addr
  let b1 ← m.readU8 (addr + 1)
  let b2 ← m.readU8 (addr + 2)
  let b3 ← m.readU8 (addr + 3)
  let b4 ← m.readU8 (addr + 4)
  let b5 ← m.readU8 (addr + 5)
  let b6 ← m.readU8 (addr + 6)
  let b7 ← m.readU8 (addr + 7)
  some (Model.word64 b0 b1 b2 b3 b4 b5 b6 b7)

def readV128LE (m : Mem) (addr : UInt64) : Option V128 := do
  let lo ← m.readU64LE addr
  let hi ← m.readU64LE (addr + 8)
  some (V128.ofHalves lo hi)

def writeU8 (m : Mem) (addr : UInt64) (b : UInt8) : Option Mem :=
  match m addr with
  | some (.rw, _) => some (fun a => if a = addr then some (.rw, b) else m a)
  | _ => none

def writeU32LE (m : Mem) (addr : UInt64) (v : UInt32) : Option Mem := do
  let m ← m.writeU8 addr v.toUInt8
  let m ← m.writeU8 (addr + 1) (v >>> 8).toUInt8
  let m ← m.writeU8 (addr + 2) (v >>> 16).toUInt8
  m.writeU8 (addr + 3) (v >>> 24).toUInt8

def writeU64LE (m : Mem) (addr : UInt64) (v : UInt64) : Option Mem := do
  let m ← m.writeU8 addr v.toUInt8
  let m ← m.writeU8 (addr + 1) (v >>> 8).toUInt8
  let m ← m.writeU8 (addr + 2) (v >>> 16).toUInt8
  let m ← m.writeU8 (addr + 3) (v >>> 24).toUInt8
  let m ← m.writeU8 (addr + 4) (v >>> 32).toUInt8
  let m ← m.writeU8 (addr + 5) (v >>> 40).toUInt8
  let m ← m.writeU8 (addr + 6) (v >>> 48).toUInt8
  m.writeU8 (addr + 7) (v >>> 56).toUInt8

def writeV128LE (m : Mem) (addr : UInt64) (v : V128) : Option Mem := do
  let m ← m.writeU64LE addr (V128.lo64 v)
  m.writeU64LE (addr + 8) (V128.lane64 v 1)

end Mem

/-- Architectural user-level A64 machine state. -/
structure ArmState where
  regs : RegFile := {}
  sp   : UInt64 := 0
  simd : SimdFile := {}
  nzcv : PState := {}
  pc   : UInt64 := 0
  mem  : Mem := fun _ => none

namespace ArmState

def getX (s : ArmState) (i : RegIdx) : UInt64 := s.regs.get i
def getW (s : ArmState) (i : RegIdx) : UInt32 := (s.regs.get i).toUInt32
def setX (s : ArmState) (i : RegIdx) (v : UInt64) : ArmState := { s with regs := s.regs.set i v }
def setW (s : ArmState) (i : RegIdx) (v : UInt32) : ArmState := { s with regs := s.regs.set i v.toUInt64 }

def getXSP (s : ArmState) (i : RegIdx) : UInt64 :=
  if i.val == 31 then s.sp else s.regs.get i

def getWSP (s : ArmState) (i : RegIdx) : UInt32 := (s.getXSP i).toUInt32

def setXSP (s : ArmState) (i : RegIdx) (v : UInt64) : ArmState :=
  if i.val == 31 then { s with sp := v } else s.setX i v

def setWSP (s : ArmState) (i : RegIdx) (v : UInt32) : ArmState :=
  s.setXSP i v.toUInt64

def getV (s : ArmState) (i : RegIdx) : V128 := s.simd.get i
def setV (s : ArmState) (i : RegIdx) (v : V128) : ArmState := { s with simd := s.simd.set i v }
def getD (s : ArmState) (i : RegIdx) : UInt64 := V128.lo64 (s.simd.get i)
def setD (s : ArmState) (i : RegIdx) (v : UInt64) : ArmState := s.setV i (V128.ofHalves v 0)

def nextPC (s : ArmState) : ArmState := { s with pc := s.pc + 4 }

end ArmState

/-! ### Bit-manipulation helpers for A64 instruction decoding and execution -/

/-- Register-operand shift kinds in A64 data-processing instructions. -/
inductive ShiftType where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

def shiftBV {w : Nat} (st : ShiftType) (x : BitVec w) (amt : Nat) : BitVec w :=
  match st with
  | .lsl => x <<< amt
  | .lsr => x >>> amt
  | .asr => BitVec.sshiftRight x amt
  | .ror =>
    if w == 0 then x
    else
      let r := amt % w
      if r == 0 then x else (x >>> r) ||| (x <<< (w - r))

/-- Logical operation kinds (`opc` in A64 logical immediate/register). -/
inductive LogicOp where
  | andOp
  | orrOp
  | eorOp
  | andsOp
  deriving DecidableEq, Repr

/-- Wide immediate move kinds (`MOVN`, `MOVZ`, `MOVK`). -/
inductive MovWideOp where
  | movn
  | movz
  | movk
  deriving DecidableEq, Repr

/-- Load/store pair addressing modes. -/
inductive PairMode where
  | postIndex
  | signedOffset
  | preIndex
  deriving DecidableEq, Repr

/-- Integer memory access width (`1, 2, 4, 8` bytes). -/
inductive MemSize where
  | b8
  | h16
  | w32
  | x64
  deriving DecidableEq, Repr

/-- Highest set bit index of a `w`-bit vector, or `none` if zero. -/
def highestSetBit {w : Nat} (bv : BitVec w) : Option Nat :=
  let rec go : Nat → Option Nat
    | 0 => none
    | k + 1 => if bv.getLsbD k then some k else go k
  go w

/-- Rotate an `esize`-bit value (stored in the low `esize` bits of `BitVec 64`)
right by `r` bits. -/
def rorElem64 (val : BitVec 64) (esize r : Nat) : BitVec 64 :=
  let mask : BitVec 64 := (1#64 <<< esize) - 1#64
  let v := val &&& mask
  let sh := r % esize
  if sh == 0 then v
  else ((v >>> sh) ||| (v <<< (esize - sh))) &&& mask

/-- Replicate the low `esize` bits across 64 bits (`esize ∈ {2, 4, 8, 16, 32, 64}`). -/
def replicateElem64 (elem : BitVec 64) (esize : Nat) : BitVec 64 :=
  let rec go (fuel acc : Nat) (cur : BitVec 64) : BitVec 64 :=
    match fuel with
    | 0 => cur
    | fuel' + 1 =>
      if acc >= 64 then cur
      else go fuel' (acc + esize) (cur ||| (elem <<< acc))
  go 64 esize elem

/-- Arm ASL `DecodeBitMasks(immN, imms, immr, TRUE, datasize)` returning the
64-bit `wmask` (truncated to 32 bits by caller when `sf = false`). -/
def decodeBitMasks64 (immN : Bool) (imms immr : BitVec 6) (sf : Bool) : Option UInt64 := do
  if !sf && immN then none
  let hi : BitVec 7 := (if immN then 1#1 else 0#1) ++ (~~~imms)
  let len ← highestSetBit hi
  if len < 1 then none
  let esize : Nat := 1 <<< len
  let datasize : Nat := if sf then 64 else 32
  if esize > datasize then none
  let levels : Nat := esize - 1
  let s : Nat := imms.toNat &&& levels
  let r : Nat := immr.toNat &&& levels
  if s == levels then none
  let welem : BitVec 64 :=
    if s + 1 >= 64 then BitVec.allOnes 64 else (1#64 <<< (s + 1)) - 1#64
  let rot := rorElem64 welem esize r
  let full := replicateElem64 rot esize
  some ⟨if sf then full else full &&& 0xFFFFFFFF#64⟩

/-- Sign-extend a `b`-bit unsigned value (`b ≤ 64`) to a wrapping `UInt64` offset. -/
def signExtend64 (b : Nat) (raw : UInt64) : UInt64 :=
  let signBit : UInt64 := 1 <<< (b - 1).toUInt64
  let mask : UInt64 := (1 <<< b.toUInt64) - 1
  let v := raw &&& mask
  if (v &&& signBit) != 0 then v ||| (~~~mask) else v

/-! ### Decoded A64 instruction syntax -/

inductive Instr where
  | b (off : UInt64)
  | bl (off : UInt64)
  | bCond (cond : Fin 16) (off : UInt64)
  | cbz (sf : Bool) (nz : Bool) (rt : RegIdx) (off : UInt64)
  | ret (rn : RegIdx)
  | adrp (rd : RegIdx) (pageOff : UInt64)
  | addSubImm (sf : Bool) (isSub : Bool) (setFlags : Bool) (rd rn : RegIdx) (imm : UInt64)
  | logicImm (sf : Bool) (op : LogicOp) (rd rn : RegIdx) (mask : UInt64)
  | movWide (sf : Bool) (op : MovWideOp) (rd : RegIdx) (imm16 : UInt16) (shift : Nat)
  | ubfm (sf : Bool) (rd rn : RegIdx) (immr imms : Nat)
  | addSubReg (sf : Bool) (isSub : Bool) (setFlags : Bool) (st : ShiftType)
      (rd rn rm : RegIdx) (amt : Nat)
  | logicReg (sf : Bool) (op : LogicOp) (st : ShiftType) (invertRm : Bool)
      (rd rn rm : RegIdx) (amt : Nat)
  | csel (sf : Bool) (cond : Fin 16) (rd rn rm : RegIdx)
  | crc32c (sz : MemSize) (rd rn rm : RegIdx)
  | madd (sf : Bool) (rd rn rm ra : RegIdx)
  | umulh (rd rn rm : RegIdx)
  | ldpGP (sf : Bool) (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  | stpGP (sf : Bool) (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  | ldpD (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  | stpD (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  /-- `LDP Qt, Qt2` and the non-temporal `LDNP Qt, Qt2` (decoded as `.signedOffset`:
  architecturally the same load, plus a cache hint that has no state effect). -/
  | ldpQ (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  /-- `STP Qt, Qt2` and the non-temporal `STNP Qt, Qt2` (decoded as `.signedOffset`). -/
  | stpQ (mode : PairMode) (rt rt2 rn : RegIdx) (off : UInt64)
  | ldrUImm (sz : MemSize) (rt rn : RegIdx) (off : UInt64)
  | strUImm (sz : MemSize) (rt rn : RegIdx) (off : UInt64)
  | ldrDImm (rt rn : RegIdx) (off : UInt64)
  | ldrQImm (rt rn : RegIdx) (off : UInt64)
  | ldrReg (sz : MemSize) (rt rn rm : RegIdx)
  | fmovXD (rd rn : RegIdx)
  | fmovDX (rd rn : RegIdx)
  | umovD (rd rn : RegIdx) (idx : Fin 2)
  | insDX (rd : RegIdx) (idx : Fin 2) (rn : RegIdx)
  | insDV (rd : RegIdx) (dstIdx : Fin 2) (rn : RegIdx) (srcIdx : Fin 2)
  | pmull1Q (rd rn rm : RegIdx)
  | eorVec (is16B : Bool) (rd rn rm : RegIdx)
  | eor3_16B (rd rn rm ra : RegIdx)
  | ext16B (rd rn rm : RegIdx) (imm4 : Fin 16)
  | zip2_2D (rd rn rm : RegIdx)
  /-- `AND Vd.16B, Vn.16B, Vm.16B`. -/
  | andVec16B (rd rn rm : RegIdx)
  /-- `USHR Vd.16B, Vn.16B, #shift` (`1 ≤ shift ≤ 8`). -/
  | ushr16B (rd rn : RegIdx) (shift : Nat)
  /-- `TBL Vd.16B, {Vn.16B}, Vm.16B` (one-register table). -/
  | tbl1_16B (rd rn rm : RegIdx)
  /-- `MOVI Vd.16B, #imm8`. -/
  | movi16B (rd : RegIdx) (imm8 : UInt8)
  deriving DecidableEq, Repr

/-! ### Bit-exact 32-bit A64 binary decoder -/

private def regAt (w : UInt32) (shift : UInt32) : RegIdx :=
  ⟨((w >>> shift) &&& 0x1F).toNat, by
    have : ((w >>> shift) &&& 0x1F).toNat < 32 := by
      rw [UInt32.toNat_and]
      exact Nat.and_lt_two_pow _ (n := 5) (by decide)
    exact this⟩

private def decodeShift2 (v : UInt32) : ShiftType :=
  match v &&& 3 with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

private def decodeLogicOp (v : UInt32) : LogicOp :=
  match v &&& 3 with
  | 0 => .andOp
  | 1 => .orrOp
  | 2 => .eorOp
  | _ => .andsOp

private def decodeMemSize (v : UInt32) : MemSize :=
  match v &&& 3 with
  | 0 => .b8
  | 1 => .h16
  | 2 => .w32
  | _ => .x64

private def decodePairMode (v : UInt32) : Option PairMode :=
  match v &&& 7 with
  | 1 => some .postIndex
  | 2 => some .signedOffset
  | 3 => some .preIndex
  | _ => none

/-- Decode a little-endian 32-bit A64 instruction word directly from its
Arm Architecture Reference Manual bit fields. -/
def decode (w : UInt32) : Option Instr :=
  let rd := regAt w 0
  let rn := regAt w 5
  let ra := regAt w 10
  let rm := regAt w 16
  let sf : Bool := ((w >>> 31) &&& 1) == 1
  -- 1. Unconditional branch immediate: B / BL
  if (w &&& 0x7C000000) == 0x14000000 then
    let off := signExtend64 28 (((w &&& 0x03FFFFFF).toUInt64) <<< 2)
    some (if sf then .bl off else .b off)
  -- 2. Conditional branch: B.cond
  else if (w &&& 0xFF000010) == 0x54000000 then
    let cond : Fin 16 := ⟨(w &&& 0xF).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 4) (by decide)⟩
    let off := signExtend64 21 ((((w >>> 5) &&& 0x7FFFF).toUInt64) <<< 2)
    some (.bCond cond off)
  -- 3. Compare and branch: CBZ / CBNZ
  else if (w &&& 0x7E000000) == 0x34000000 then
    let nz : Bool := ((w >>> 24) &&& 1) == 1
    let off := signExtend64 21 ((((w >>> 5) &&& 0x7FFFF).toUInt64) <<< 2)
    some (.cbz sf nz rd off)
  -- 4. RET Xn
  else if (w &&& 0xFFFFFC1F) == 0xD65F0000 then
    some (.ret rn)
  -- 5. ADRP
  else if (w &&& 0x9F000000) == 0x90000000 then
    let immlo := ((w >>> 29) &&& 0x3).toUInt64
    let immhi := ((w >>> 5) &&& 0x7FFFF).toUInt64
    let pageOff := (signExtend64 21 ((immhi <<< 2) ||| immlo)) <<< 12
    some (.adrp rd pageOff)
  -- 6. Add/subtract immediate
  else if (w &&& 0x1F800000) == 0x11000000 then
    let isSub : Bool := ((w >>> 30) &&& 1) == 1
    let setFlags : Bool := ((w >>> 29) &&& 1) == 1
    let sh : Bool := ((w >>> 22) &&& 1) == 1
    let imm12 := ((w >>> 10) &&& 0xFFF).toUInt64
    let imm := if sh then imm12 <<< 12 else imm12
    some (.addSubImm sf isSub setFlags rd rn imm)
  -- 7. Logical immediate
  else if (w &&& 0x1F800000) == 0x12000000 then do
    let op := decodeLogicOp (w >>> 29)
    let immN : Bool := ((w >>> 22) &&& 1) == 1
    let immr : BitVec 6 := BitVec.ofNat 6 ((w >>> 16) &&& 0x3F).toNat
    let imms : BitVec 6 := BitVec.ofNat 6 ((w >>> 10) &&& 0x3F).toNat
    let mask ← decodeBitMasks64 immN imms immr sf
    some (.logicImm sf op rd rn mask)
  -- 8. Move wide immediate (MOVN / MOVZ / MOVK)
  else if (w &&& 0x1F800000) == 0x12800000 then
    let opc := (w >>> 29) &&& 0x3
    let hw := ((w >>> 21) &&& 0x3).toNat
    if !sf && hw >= 2 then none
    else
      let imm16 := ((w >>> 5) &&& 0xFFFF).toUInt16
      match opc with
      | 0 => some (.movWide sf .movn rd imm16 (hw * 16))
      | 2 => some (.movWide sf .movz rd imm16 (hw * 16))
      | 3 => some (.movWide sf .movk rd imm16 (hw * 16))
      | _ => none
  -- 9. Unsigned bitfield move UBFM (LSL / LSR / UBFIZ / UBFX)
  else if (w &&& 0x7F800000) == 0x53000000 then
    let immN : Bool := ((w >>> 22) &&& 1) == 1
    let immr := ((w >>> 16) &&& 0x3F).toNat
    let imms := ((w >>> 10) &&& 0x3F).toNat
    if immN != sf then none
    else if !sf && (immr >= 32 || imms >= 32) then none
    else some (.ubfm sf rd rn immr imms)
  -- 10. Add/subtract shifted register
  else if (w &&& 0x1F200000) == 0x0B000000 then
    let isSub : Bool := ((w >>> 30) &&& 1) == 1
    let setFlags : Bool := ((w >>> 29) &&& 1) == 1
    let shBits := (w >>> 22) &&& 0x3
    let amt := ((w >>> 10) &&& 0x3F).toNat
    if shBits == 3 then none
    else if !sf && amt >= 32 then none
    else some (.addSubReg sf isSub setFlags (decodeShift2 shBits) rd rn rm amt)
  -- 11. Logical shifted register
  else if (w &&& 0x1F000000) == 0x0A000000 then
    let op := decodeLogicOp (w >>> 29)
    let shBits := (w >>> 22) &&& 0x3
    let inv : Bool := ((w >>> 21) &&& 1) == 1
    let amt := ((w >>> 10) &&& 0x3F).toNat
    if !sf && amt >= 32 then none
    else some (.logicReg sf op (decodeShift2 shBits) inv rd rn rm amt)
  -- 12. Conditional select CSEL
  else if (w &&& 0x7FE00C00) == 0x1A800000 then
    let cond : Fin 16 := ⟨((w >>> 12) &&& 0xF).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 4) (by decide)⟩
    some (.csel sf cond rd rn rm)
  -- 13. CRC32C{B,H,W,X}
  else if (w &&& 0x7FE0F000) == 0x1AC05000 then
    let szBits := (w >>> 10) &&& 0x3
    if (sf && szBits != 3) || (!sf && szBits == 3) then none
    else some (.crc32c (decodeMemSize szBits) rd rn rm)
  -- 14. MADD (including MUL when Ra = 31)
  else if (w &&& 0x7FE08000) == 0x1B000000 then
    some (.madd sf rd rn rm ra)
  -- 15. UMULH Xd, Xn, Xm
  else if (w &&& 0xFFE0FC00) == 0x9BC07C00 then
    some (.umulh rd rn rm)
  -- 16a. Non-temporal SIMD pair `LDNP / STNP Qt, Qt2, [Xn|SP, #imm]`: the same
  -- load/store as the signed-offset `LDP / STP Qt, Qt2`, with a cache hint.
  else if (w &&& 0xFF800000) == 0xAC000000 then
    let isLoad : Bool := ((w >>> 22) &&& 1) == 1
    let off := signExtend64 7 (((w >>> 15) &&& 0x7F).toUInt64) <<< 4
    if isLoad && rd == ra then none
    else some (if isLoad then .ldpQ .signedOffset rd ra rn off
               else .stpQ .signedOffset rd ra rn off)
  -- 16. Load/store register pair (GP 32/64-bit, SIMD 64-bit D and 128-bit Q)
  else if (w &&& 0x3A000000) == 0x28000000 then do
    let opc := (w >>> 30) &&& 0x3
    let isSimd : Bool := ((w >>> 26) &&& 1) == 1
    let mode ← decodePairMode (w >>> 23)
    let isLoad : Bool := ((w >>> 22) &&& 1) == 1
    let imm7 := signExtend64 7 (((w >>> 15) &&& 0x7F).toUInt64)
    let wb : Bool := mode != .signedOffset
    if !isSimd && (opc == 0 || opc == 2) then
      let is64 : Bool := opc == 2
      let off := imm7 <<< (if is64 then 3 else 2)
      -- Enforce architectural constrained-unpredictable exclusions:
      if isLoad && rd == ra && rd.val != 31 then none
      else if wb && (rd == rn || ra == rn) && rn.val != 31 then none
      else some (if isLoad then .ldpGP is64 mode rd ra rn off else .stpGP is64 mode rd ra rn off)
    else if isSimd && opc == 1 then
      let off := imm7 <<< 3
      if isLoad && rd == ra then none
      else some (if isLoad then .ldpD mode rd ra rn off else .stpD mode rd ra rn off)
    else if isSimd && opc == 2 then
      let off := imm7 <<< 4
      if isLoad && rd == ra then none
      else some (if isLoad then .ldpQ mode rd ra rn off else .stpQ mode rd ra rn off)
    else none
  -- 17. Load/store unsigned immediate (GP 8/16/32/64-bit and SIMD D/Q)
  else if (w &&& 0x3B000000) == 0x39000000 then
    let szBits := (w >>> 30) &&& 0x3
    let isSimd : Bool := ((w >>> 26) &&& 1) == 1
    let opc := (w >>> 22) &&& 0x3
    let imm12 := ((w >>> 10) &&& 0xFFF).toUInt64
    if !isSimd && (opc == 0 || opc == 1) then
      let sz := decodeMemSize szBits
      let off := imm12 <<< szBits.toUInt64
      some (if opc == 1 then .ldrUImm sz rd rn off else .strUImm sz rd rn off)
    else if isSimd && szBits == 3 && opc == 1 then
      some (.ldrDImm rd rn (imm12 <<< 3))
    else if isSimd && szBits == 0 && opc == 3 then
      some (.ldrQImm rd rn (imm12 <<< 4))
    else none
  -- 18. Load register offset (LDRB / LDRH Wt, [Xn, Xm])
  else if (w &&& 0x3FE0FC00) == 0x38606800 then
    let szBits := (w >>> 30) &&& 0x3
    if szBits == 0 || szBits == 1 then
      some (.ldrReg (decodeMemSize szBits) rd rn rm)
    else none
  -- 19. SIMD / FP transfers, crypto, and permutes
  else if (w &&& 0xFFFFFC00) == 0x9E660000 then
    some (.fmovXD rd rn)
  else if (w &&& 0xFFFFFC00) == 0x9E670000 then
    some (.fmovDX rd rn)
  else if (w &&& 0xFFEFFC00) == 0x4E083C00 then
    let idx : Fin 2 := ⟨((w >>> 20) &&& 1).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 1) (by decide)⟩
    some (.umovD rd rn idx)
  else if (w &&& 0xFFEFFC00) == 0x4E081C00 then
    let idx : Fin 2 := ⟨((w >>> 20) &&& 1).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 1) (by decide)⟩
    some (.insDX rd idx rn)
  else if (w &&& 0xFFEFBC00) == 0x6E080400 then
    let dstIdx : Fin 2 := ⟨((w >>> 20) &&& 1).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 1) (by decide)⟩
    let srcIdx : Fin 2 := ⟨((w >>> 14) &&& 1).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 1) (by decide)⟩
    some (.insDV rd dstIdx rn srcIdx)
  else if (w &&& 0xFFE0FC00) == 0x0EE0E000 then
    some (.pmull1Q rd rn rm)
  else if (w &&& 0xBFE0FC00) == 0x2E201C00 then
    let q : Bool := ((w >>> 30) &&& 1) == 1
    some (.eorVec q rd rn rm)
  else if (w &&& 0xFFE08000) == 0xCE000000 then
    some (.eor3_16B rd rn rm ra)
  else if (w &&& 0xFFE08400) == 0x6E000000 then
    let imm4 : Fin 16 := ⟨((w >>> 11) &&& 0xF).toNat, by
      rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ (n := 4) (by decide)⟩
    some (.ext16B rd rn rm imm4)
  else if (w &&& 0xFFE0FC00) == 0x4EC07800 then
    some (.zip2_2D rd rn rm)
  -- 20. Byte-lane vector operations on `.16B` (AND, TBL with one table register,
  -- USHR with byte lanes, MOVI with an 8-bit immediate replicated to every byte)
  else if (w &&& 0xFFE0FC00) == 0x4E201C00 then
    some (.andVec16B rd rn rm)
  else if (w &&& 0xFFE0FC00) == 0x4E000000 then
    some (.tbl1_16B rd rn rm)
  else if (w &&& 0xFFF8FC00) == 0x6F080400 then
    some (.ushr16B rd rn (8 - ((w >>> 16) &&& 0x7).toNat))
  else if (w &&& 0xFFF8FC00) == 0x4F00E400 then
    some (.movi16B rd ((((w >>> 16) &&& 0x7) <<< 5) ||| ((w >>> 5) &&& 0x1F)).toUInt8)
  else
    none

/-! ### Operational instruction semantics -/

/-- Execute `UBFM` on an `N`-bit operand (`N ∈ {32, 64}`). -/
def evalUbfm {w : Nat} (src : BitVec w) (immr imms : Nat) : BitVec w :=
  if imms >= immr then
    let width := imms - immr + 1
    let mask : BitVec w :=
      if width >= w then BitVec.allOnes w else (BitVec.ofNat w 1 <<< width) - BitVec.ofNat w 1
    (src >>> immr) &&& mask
  else
    let width := imms + 1
    let mask : BitVec w :=
      if width >= w then BitVec.allOnes w else (BitVec.ofNat w 1 <<< width) - BitVec.ofNat w 1
    (src &&& mask) <<< (w - immr)

/-- `ZIP2 Vd.2D, Vn.2D, Vm.2D`: interleave the upper 64-bit lanes of `Vn` and `Vm`. -/
def zip2_2d (vn vm : V128) : V128 :=
  V128.ofHalves (V128.hi64 vn) (V128.hi64 vm)

/-- `EOR Vd.8B, Vn.8B, Vm.8B` (`Q = 0`): XOR low 64-bit halves and zero upper 64 bits. -/
def veor8b (vn vm : V128) : V128 :=
  V128.ofHalves (V128.lo64 vn ^^^ V128.lo64 vm) 0

/-- `EOR3 Vd.16B, Vn.16B, Vm.16B, Va.16B` (Armv8.2-SHA3 three-way 128-bit XOR). -/
def veor3q (vn vm va : V128) : V128 :=
  Model.veorq (Model.veorq vn vm) va

/-- `INS Vd.D[idx], val`: insert a 64-bit value into lane `idx` of `Vd`, preserving the other lane. -/
def insLane64 (vd : V128) (idx : Fin 2) (val : UInt64) : V128 :=
  if idx.val == 0 then V128.ofHalves val (V128.hi64 vd)
  else V128.ofHalves (V128.lo64 vd) val

/-- Execute a single decoded A64 instruction on `s`. Returns `none` on any
unmapped or permission-violating memory access. -/
def execInstr (s : ArmState) (ins : Instr) : Option ArmState :=
  match ins with
  | .b off =>
    some { s with pc := s.pc + off }
  | .bl off =>
    some { (s.setX ⟨30, by decide⟩ (s.pc + 4)) with pc := s.pc + off }
  | .bCond cond off =>
    if conditionHolds cond s.nzcv then some { s with pc := s.pc + off }
    else some s.nextPC
  | .cbz sf nz rt off =>
    let isZero := if sf then s.getX rt == 0 else s.getW rt == 0
    if isZero != nz then some { s with pc := s.pc + off }
    else some s.nextPC
  | .ret rn =>
    some { s with pc := s.getX rn }
  | .adrp rd pageOff =>
    let basePage := s.pc &&& 0xFFFFFFFFFFFFF000
    some (s.setX rd (basePage + pageOff)).nextPC
  | .addSubImm sf isSub setFlags rd rn imm =>
    if sf then
      let op1 := (s.getXSP rn).toBitVec
      let op2 := if isSub then ~~~imm.toBitVec else imm.toBitVec
      if setFlags then
        let (res, flags) := addWithCarry op1 op2 isSub
        some { (s.setX rd ⟨res⟩) with nzcv := flags, pc := s.pc + 4 }
      else
        let res := if isSub then s.getXSP rn - imm else s.getXSP rn + imm
        some (s.setXSP rd res).nextPC
    else
      let op1 := (s.getWSP rn).toBitVec
      let op2 := if isSub then ~~~imm.toUInt32.toBitVec else imm.toUInt32.toBitVec
      if setFlags then
        let (res, flags) := addWithCarry op1 op2 isSub
        some { (s.setW rd ⟨res⟩) with nzcv := flags, pc := s.pc + 4 }
      else
        let res := if isSub then s.getWSP rn - imm.toUInt32 else s.getWSP rn + imm.toUInt32
        some (s.setWSP rd res).nextPC
  | .logicImm sf op rd rn mask =>
    if sf then
      let a := s.getX rn
      let res : UInt64 :=
        match op with
        | .andOp | .andsOp => a &&& mask
        | .orrOp => a ||| mask
        | .eorOp => a ^^^ mask
      if op == .andsOp then
        let flags : PState := { n := res.toBitVec.msb, z := res == 0, c := false, v := false }
        some { (s.setX rd res) with nzcv := flags, pc := s.pc + 4 }
      else
        some (s.setXSP rd res).nextPC
    else
      let a := s.getW rn
      let m32 := mask.toUInt32
      let res : UInt32 :=
        match op with
        | .andOp | .andsOp => a &&& m32
        | .orrOp => a ||| m32
        | .eorOp => a ^^^ m32
      if op == .andsOp then
        let flags : PState := { n := res.toBitVec.msb, z := res == 0, c := false, v := false }
        some { (s.setW rd res) with nzcv := flags, pc := s.pc + 4 }
      else
        some (s.setWSP rd res).nextPC
  | .movWide sf op rd imm16 shift =>
    if sf then
      let piece : UInt64 := imm16.toUInt64 <<< shift.toUInt64
      let res : UInt64 :=
        match op with
        | .movz => piece
        | .movn => ~~~piece
        | .movk =>
          let clrMask : UInt64 := ~~~(0xFFFF <<< shift.toUInt64)
          (s.getX rd &&& clrMask) ||| piece
      some (s.setX rd res).nextPC
    else
      let piece : UInt32 := imm16.toUInt32 <<< shift.toUInt32
      let res : UInt32 :=
        match op with
        | .movz => piece
        | .movn => ~~~piece
        | .movk =>
          let clrMask : UInt32 := ~~~(0xFFFF <<< shift.toUInt32)
          (s.getW rd &&& clrMask) ||| piece
      some (s.setW rd res).nextPC
  | .ubfm sf rd rn immr imms =>
    if sf then
      some (s.setX rd ⟨evalUbfm (s.getX rn).toBitVec immr imms⟩).nextPC
    else
      some (s.setW rd ⟨evalUbfm (s.getW rn).toBitVec immr imms⟩).nextPC
  | .addSubReg sf isSub setFlags st rd rn rm amt =>
    if sf then
      let op1 := (s.getX rn).toBitVec
      let shifted := shiftBV st (s.getX rm).toBitVec amt
      let op2 := if isSub then ~~~shifted else shifted
      if setFlags then
        let (res, flags) := addWithCarry op1 op2 isSub
        some { (s.setX rd ⟨res⟩) with nzcv := flags, pc := s.pc + 4 }
      else
        let res : UInt64 := if isSub then s.getX rn - ⟨shifted⟩ else s.getX rn + ⟨shifted⟩
        some (s.setX rd res).nextPC
    else
      let op1 := (s.getW rn).toBitVec
      let shifted := shiftBV st (s.getW rm).toBitVec amt
      let op2 := if isSub then ~~~shifted else shifted
      if setFlags then
        let (res, flags) := addWithCarry op1 op2 isSub
        some { (s.setW rd ⟨res⟩) with nzcv := flags, pc := s.pc + 4 }
      else
        let res : UInt32 := if isSub then s.getW rn - ⟨shifted⟩ else s.getW rn + ⟨shifted⟩
        some (s.setW rd res).nextPC
  | .logicReg sf op st invertRm rd rn rm amt =>
    if sf then
      let a := s.getX rn
      let b0 : UInt64 := ⟨shiftBV st (s.getX rm).toBitVec amt⟩
      let b := if invertRm then ~~~b0 else b0
      let res : UInt64 :=
        match op with
        | .andOp | .andsOp => a &&& b
        | .orrOp => a ||| b
        | .eorOp => a ^^^ b
      if op == .andsOp then
        let flags : PState := { n := res.toBitVec.msb, z := res == 0, c := false, v := false }
        some { (s.setX rd res) with nzcv := flags, pc := s.pc + 4 }
      else
        some (s.setX rd res).nextPC
    else
      let a := s.getW rn
      let b0 : UInt32 := ⟨shiftBV st (s.getW rm).toBitVec amt⟩
      let b := if invertRm then ~~~b0 else b0
      let res : UInt32 :=
        match op with
        | .andOp | .andsOp => a &&& b
        | .orrOp => a ||| b
        | .eorOp => a ^^^ b
      if op == .andsOp then
        let flags : PState := { n := res.toBitVec.msb, z := res == 0, c := false, v := false }
        some { (s.setW rd res) with nzcv := flags, pc := s.pc + 4 }
      else
        some (s.setW rd res).nextPC
  | .csel sf cond rd rn rm =>
    let hold := conditionHolds cond s.nzcv
    if sf then
      some (s.setX rd (if hold then s.getX rn else s.getX rm)).nextPC
    else
      some (s.setW rd (if hold then s.getW rn else s.getW rm)).nextPC
  | .crc32c sz rd rn rm =>
    let acc := s.getW rn
    let res :=
      match sz with
      | .b8  => Model.crc32c_u8 acc (s.getW rm).toUInt8
      | .h16 => Model.crc32c_u16 acc (s.getW rm).toUInt16
      | .w32 => Model.crc32c_u32 acc (s.getW rm)
      | .x64 => Model.crc32c_u64 acc (s.getX rm)
    some (s.setW rd res).nextPC
  | .madd sf rd rn rm ra =>
    if sf then
      some (s.setX rd (s.getX ra + s.getX rn * s.getX rm)).nextPC
    else
      some (s.setW rd (s.getW ra + s.getW rn * s.getW rm)).nextPC
  | .umulh rd rn rm =>
    let prod : Nat := (s.getX rn).toNat * (s.getX rm).toNat
    some (s.setX rd (UInt64.ofNat (prod >>> 64))).nextPC
  | .ldpGP sf mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let s1 ←
      if sf then do
        let v1 ← s.mem.readU64LE addr
        let v2 ← s.mem.readU64LE (addr + 8)
        some ((s.setX rt v1).setX rt2 v2)
      else do
        let v1 ← s.mem.readU32LE addr
        let v2 ← s.mem.readU32LE (addr + 4)
        some ((s.setW rt v1).setW rt2 v2)
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .stpGP sf mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let m' ←
      if sf then do
        let m1 ← s.mem.writeU64LE addr (s.getX rt)
        m1.writeU64LE (addr + 8) (s.getX rt2)
      else do
        let m1 ← s.mem.writeU32LE addr (s.getW rt)
        m1.writeU32LE (addr + 4) (s.getW rt2)
    let s1 := { s with mem := m' }
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .ldpD mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let v1 ← s.mem.readU64LE addr
    let v2 ← s.mem.readU64LE (addr + 8)
    let s1 := (s.setD rt v1).setD rt2 v2
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .stpD mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let m1 ← s.mem.writeU64LE addr (s.getD rt)
    let m2 ← m1.writeU64LE (addr + 8) (s.getD rt2)
    let s1 := { s with mem := m2 }
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .ldpQ mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let v1 ← s.mem.readV128LE addr
    let v2 ← s.mem.readV128LE (addr + 16)
    let s1 := (s.setV rt v1).setV rt2 v2
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .stpQ mode rt rt2 rn off => do
    let base := s.getXSP rn
    let addr := if mode == .postIndex then base else base + off
    let m1 ← s.mem.writeV128LE addr (s.getV rt)
    let m2 ← m1.writeV128LE (addr + 16) (s.getV rt2)
    let s1 := { s with mem := m2 }
    let s2 := if mode == .signedOffset then s1 else s1.setXSP rn (base + off)
    some s2.nextPC
  | .ldrUImm sz rt rn off => do
    let addr := s.getXSP rn + off
    match sz with
    | .b8  => let v ← s.mem.readU8 addr; some (s.setW rt v.toUInt32).nextPC
    | .h16 => let v ← s.mem.readU16LE addr; some (s.setW rt v.toUInt32).nextPC
    | .w32 => let v ← s.mem.readU32LE addr; some (s.setW rt v).nextPC
    | .x64 => let v ← s.mem.readU64LE addr; some (s.setX rt v).nextPC
  | .strUImm sz rt rn off => do
    let addr := s.getXSP rn + off
    let m' ←
      match sz with
      | .b8  => s.mem.writeU8 addr (s.getW rt).toUInt8
      | .h16 => do
        let v := (s.getW rt).toUInt16
        let m1 ← s.mem.writeU8 addr v.toUInt8
        m1.writeU8 (addr + 1) (v >>> 8).toUInt8
      | .w32 => s.mem.writeU32LE addr (s.getW rt)
      | .x64 => s.mem.writeU64LE addr (s.getX rt)
    some { s with mem := m', pc := s.pc + 4 }
  | .ldrDImm rt rn off => do
    let v ← s.mem.readU64LE (s.getXSP rn + off)
    some (s.setD rt v).nextPC
  | .ldrQImm rt rn off => do
    let v ← s.mem.readV128LE (s.getXSP rn + off)
    some (s.setV rt v).nextPC
  | .ldrReg sz rt rn rm => do
    let addr := s.getXSP rn + s.getX rm
    match sz with
    | .b8  => let v ← s.mem.readU8 addr; some (s.setW rt v.toUInt32).nextPC
    | .h16 => let v ← s.mem.readU16LE addr; some (s.setW rt v.toUInt32).nextPC
    | .w32 => let v ← s.mem.readU32LE addr; some (s.setW rt v).nextPC
    | .x64 => let v ← s.mem.readU64LE addr; some (s.setX rt v).nextPC
  | .fmovXD rd rn =>
    some (s.setX rd (s.getD rn)).nextPC
  | .fmovDX rd rn =>
    some (s.setD rd (s.getX rn)).nextPC
  | .umovD rd rn idx =>
    some (s.setX rd (V128.lane64 (s.getV rn) idx)).nextPC
  | .insDX rd idx rn =>
    some (s.setV rd (insLane64 (s.getV rd) idx (s.getX rn))).nextPC
  | .insDV rd dstIdx rn srcIdx =>
    some (s.setV rd (insLane64 (s.getV rd) dstIdx (V128.lane64 (s.getV rn) srcIdx))).nextPC
  | .pmull1Q rd rn rm =>
    some (s.setV rd (Model.vmull_p64 (s.getV rn) (s.getV rm))).nextPC
  | .eorVec is16B rd rn rm =>
    let v := if is16B then Model.veorq (s.getV rn) (s.getV rm)
             else veor8b (s.getV rn) (s.getV rm)
    some (s.setV rd v).nextPC
  | .eor3_16B rd rn rm ra =>
    some (s.setV rd (veor3q (s.getV rn) (s.getV rm) (s.getV ra))).nextPC
  | .ext16B rd rn rm imm4 =>
    some (s.setV rd (Model.vextq (s.getV rn) (s.getV rm) imm4)).nextPC
  | .zip2_2D rd rn rm =>
    some (s.setV rd (zip2_2d (s.getV rn) (s.getV rm))).nextPC
  | .andVec16B rd rn rm =>
    some (s.setV rd (Model.vandq (s.getV rn) (s.getV rm))).nextPC
  | .ushr16B rd rn shift =>
    some (s.setV rd (Model.vshrq_n_u8 (s.getV rn) shift)).nextPC
  | .tbl1_16B rd rn rm =>
    some (s.setV rd (Model.vqtbl1q_u8 (s.getV rn) (s.getV rm))).nextPC
  | .movi16B rd imm8 =>
    some (s.setV rd (Model.vdupq_n_u8 imm8)).nextPC

/-- Fetch the 32-bit instruction word at `s.pc` from `code`, decode it, and
execute one architectural step. -/
def step (code : UInt64 → Option UInt32) (s : ArmState) : Option ArmState := do
  let w ← code s.pc
  let ins ← decode w
  execInstr s ins

/-- Execute `n` architectural A64 instructions starting from `s`. -/
def run (code : UInt64 → Option UInt32) : Nat → ArmState → Option ArmState
  | 0, s => some s
  | n + 1, s => do
    let s' ← step code s
    run code n s'

end SimdModels.Arm64
