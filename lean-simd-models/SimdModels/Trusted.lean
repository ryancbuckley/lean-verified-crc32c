/-
THE TRUSTED INSTRUCTION BINDINGS. This is the only file in the project that
may contain `@[extern]`. Each declaration binds one CPU instruction (through
a one-line macro in `c/simd_shim.h`) to its Lean model in `SimdModels.Models`.

Compiled code calls the instruction. Proofs see the model. That the two agree
is an assumption, invisible to `#print axioms`; this file is its record.
`scripts/check_trusted.sh` checks that no other file uses `extern`,
`implemented_by`, `axiom`, `sorry` or `native_decide`.

| Binding      | AArch64 instruction    | x86-64 instruction            |
| ------------ | ---------------------- | ----------------------------- |
| `crc32c_u8`  | `CRC32CB`              | `CRC32 r32, r/m8`             |
| `crc32c_u16` | `CRC32CH`              | `CRC32 r32, r/m16`            |
| `crc32c_u32` | `CRC32CW`              | `CRC32 r32, r/m32`            |
| `crc32c_u64` | `CRC32CX`              | `CRC32 r64, r/m64`            |
| `clmulLo`    | `PMULL` (low half)     | `PCLMULQDQ imm 0` (low half)  |
| `clmulHi`    | `PMULL` (high half)    | `PCLMULQDQ imm 0` (high half) |
| `loadU64LE`  | `LDR Xt` / `LDR Qt` ½  | `MOV r64, m64` / `MOVDQU` ½   |
-/
import SimdModels.Models

namespace SimdModels

@[extern c inline "SIMDMODELS_CRC32C_U8(#1, #2)"]
def crc32c_u8 (c : UInt32) (v : UInt8) : UInt32 := Model.crc32c_u8 c v

@[extern c inline "SIMDMODELS_CRC32C_U16(#1, #2)"]
def crc32c_u16 (c : UInt32) (v : UInt16) : UInt32 := Model.crc32c_u16 c v

@[extern c inline "SIMDMODELS_CRC32C_U32(#1, #2)"]
def crc32c_u32 (c : UInt32) (v : UInt32) : UInt32 := Model.crc32c_u32 c v

@[extern c inline "SIMDMODELS_CRC32C_U64(#1, #2)"]
def crc32c_u64 (c : UInt32) (v : UInt64) : UInt32 := Model.crc32c_u64 c v

@[extern c inline "SIMDMODELS_CLMUL_LO(#1, #2)"]
def clmulLo (a b : UInt64) : UInt64 := Model.clmulLo a b

@[extern c inline "SIMDMODELS_CLMUL_HI(#1, #2)"]
def clmulHi (a b : UInt64) : UInt64 := Model.clmulHi a b

@[extern c inline "SIMDMODELS_LOAD_U64_LE(#1, #2)"]
def loadU64LE (a : @& ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) : UInt64 :=
  Model.loadU64LE a i hs h

end SimdModels
