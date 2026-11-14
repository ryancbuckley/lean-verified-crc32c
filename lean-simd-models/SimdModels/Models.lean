/-
Instruction models: pure Lean definitions, written in the shape of the vendor
pseudocode, for the instructions bound in `SimdModels.Trusted`. Imports only
Lean core, so native binaries never link Mathlib. No `extern` here: these are
ordinary definitions, and the proofs in `SimdModels.Semantics` are about them.
-/

namespace SimdModels.Model

/-! ### CRC32C (Arm `CRC32C<B,H,W,X>`, x86 SSE4.2 `CRC32`)

Arm ASL, `aarch64/instrs/integer/crc`:

    bits(32)   acc     = X[n];
    bits(size) val     = X[m];
    bits(32)   poly    = 0x1EDC6F41<31:0>;
    bits(32+size) tempacc = BitReverse(acc) : Zeros(size);
    bits(size+32) tempval = BitReverse(val) : Zeros(32);
    X[d] = BitReverse(Poly32Mod2(tempacc EOR tempval, poly));

    bits(32) Poly32Mod2(bits(N) data, bits(32) poly)
        assert N > 32;
        for i = N-1 downto 32
            if data<i> == '1' then
                data<i-1:0> = data<i-1:0> EOR (poly:Zeros(i-32));
        return data<31:0>;

Intel SDM, `CRC32`, has the same shape: bit-reflect both operands, shift,
XOR, reduce modulo `11EDC6F41H`, bit-reflect the result.
-/

/-- The loop of ASL `Poly32Mod2`, for `i = 32 + k - 1` down to `32`. -/
def poly32Mod2Loop {n : Nat} (poly : BitVec 32) : Nat → BitVec n → BitVec n
  | 0, data => data
  | k + 1, data =>
    poly32Mod2Loop poly k
      (if data.getLsbD (32 + k) then data ^^^ (poly.setWidth n <<< k) else data)

/-- ASL `Poly32Mod2`. -/
def poly32Mod2 {n : Nat} (data : BitVec n) (poly : BitVec 32) : BitVec 32 :=
  (poly32Mod2Loop poly (n - 32) data).setWidth 32

/-- The CRC32C polynomial constant as it appears in the Arm and Intel manuals. -/
def crc32cPoly : BitVec 32 := 0x1EDC6F41#32

/-- `CRC32C` with a `size`-bit data operand. -/
def crc32c (size : Nat) (acc : BitVec 32) (val : BitVec size) : BitVec 32 :=
  let tempacc : BitVec (32 + size) := acc.reverse ++ (0 : BitVec size)
  let tempval : BitVec (32 + size) := (val.reverse ++ (0 : BitVec 32)).cast (Nat.add_comm size 32)
  (poly32Mod2 (tempacc ^^^ tempval) crc32cPoly).reverse

def crc32c_u8 (c : UInt32) (v : UInt8) : UInt32 := ⟨crc32c 8 c.toBitVec v.toBitVec⟩
def crc32c_u16 (c : UInt32) (v : UInt16) : UInt32 := ⟨crc32c 16 c.toBitVec v.toBitVec⟩
def crc32c_u32 (c : UInt32) (v : UInt32) : UInt32 := ⟨crc32c 32 c.toBitVec v.toBitVec⟩
def crc32c_u64 (c : UInt32) (v : UInt64) : UInt32 := ⟨crc32c 64 c.toBitVec v.toBitVec⟩

/-! ### Carry-less multiply (Arm `PMULL`, x86 `PCLMULQDQ`)

Arm ASL `PolynomialMult`:

    bits(M+N) result = Zeros(M+N);
    bits(M+N) extended_op2 = ZeroExtend(op2, M+N);
    for i = 0 to M-1
        if op1<i> == '1' then
            result = result EOR LSL(extended_op2, i);
    return result;
-/

/-- The loop of ASL `PolynomialMult`, for `i = 0` to `k - 1`. -/
def polynomialMultLoop (op1 : BitVec 64) (ext2 : BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | k + 1 =>
    let r := polynomialMultLoop op1 ext2 k
    if op1.getLsbD k then r ^^^ (ext2 <<< k) else r

/-- ASL `PolynomialMult` for two 64-bit operands. -/
def polynomialMult (op1 op2 : BitVec 64) : BitVec 128 :=
  polynomialMultLoop op1 (op2.setWidth 128) 64

/-- Low 64 bits of the 64x64 carry-less product. -/
def clmulLo (a b : UInt64) : UInt64 := ⟨(polynomialMult a.toBitVec b.toBitVec).setWidth 64⟩

/-- High 64 bits of the 64x64 carry-less product. -/
def clmulHi (a b : UInt64) : UInt64 := ⟨((polynomialMult a.toBitVec b.toBitVec) >>> 64).setWidth 64⟩

end SimdModels.Model
