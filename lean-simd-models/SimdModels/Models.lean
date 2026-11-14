/-
Instruction models: pure Lean definitions, written in the shape of the vendor
pseudocode, for the instructions bound in `SimdModels.Trusted` plus pure 128-bit
SIMD register and lane views (`V128`). Imports only Lean core, so native
binaries never link Mathlib. No `extern` here: these are ordinary definitions,
and the proofs in `SimdModels.Semantics`, `SimdModels.V128`, and
`SimdModels.IntelSdm` are about them.
-/

namespace SimdModels

/-- A 128-bit SIMD vector register (`uint8x16_t` / `poly128_t` / `__m128i`),
with lane 0 in the least-significant bits (little-endian register convention on
both AArch64 and x86-64). -/
abbrev V128 := BitVec 128

namespace V128

/-- Construct a `V128` from its low (`[63:0]`) and high (`[127:64]`) quadwords. -/
def ofHalves (lo hi : UInt64) : V128 := hi.toBitVec ++ lo.toBitVec

/-- Low 64-bit lane (`[63:0]`). -/
def lo64 (v : V128) : UInt64 := ⟨v.setWidth 64⟩

/-- High 64-bit lane (`[127:64]`). -/
def hi64 (v : V128) : UInt64 := ⟨(v >>> 64).setWidth 64⟩

/-- Extract 8-bit lane `i` (`0 ≤ i < 16`). -/
def lane8 (v : V128) (i : Fin 16) : UInt8 := ⟨(v >>> (8 * i.val)).setWidth 8⟩

/-- Extract 16-bit lane `i` (`0 ≤ i < 8`). -/
def lane16 (v : V128) (i : Fin 8) : UInt16 := ⟨(v >>> (16 * i.val)).setWidth 16⟩

/-- Extract 32-bit lane `i` (`0 ≤ i < 4`). -/
def lane32 (v : V128) (i : Fin 4) : UInt32 := ⟨(v >>> (32 * i.val)).setWidth 32⟩

/-- Extract 64-bit lane `i` (`0 ≤ i < 2`). -/
def lane64 (v : V128) (i : Fin 2) : UInt64 := ⟨(v >>> (64 * i.val)).setWidth 64⟩

/-- All sixteen 8-bit lanes, from lane 0 to lane 15. -/
def lanes8 (v : V128) : List UInt8 := List.ofFn (lane8 v)

/-- All eight 16-bit lanes, from lane 0 to lane 7. -/
def lanes16 (v : V128) : List UInt16 := List.ofFn (lane16 v)

/-- All four 32-bit lanes, from lane 0 to lane 3. -/
def lanes32 (v : V128) : List UInt32 := List.ofFn (lane32 v)

/-- Both 64-bit lanes `[lo64 v, hi64 v]`. -/
def lanes64 (v : V128) : List UInt64 := List.ofFn (lane64 v)

end V128

namespace Model

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
XOR, reduce modulo `11EDC6F41H`, bit-reflect the result (formally proven equal
in `SimdModels.IntelSdm`).
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

/-! ### Carry-less multiply (Arm `PMULL` / `PMULL2`, x86 `PCLMULQDQ`)

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

/-! ### 128-bit vector operations (Arm Neon / x86 SSE2–PCLMULQDQ) -/

/-- `EOR v.16b` / `veorq_u8` / `_mm_xor_si128`. -/
def veorq (a b : V128) : V128 := a ^^^ b

/-- `EXT v.16b, a.16b, b.16b, #imm` / `vextq_u8` / `_mm_alignr_epi8(b, a, imm)`. -/
def vextq (a b : V128) (imm : Fin 16) : V128 :=
  ((b ++ a) >>> (8 * imm.val)).setWidth 128

/-- `PMULL v.1q, a.1d, b.1d` (`vmull_p64`): carry-less product of low 64-bit lanes. -/
def vmull_p64 (a b : V128) : V128 :=
  polynomialMult (V128.lo64 a).toBitVec (V128.lo64 b).toBitVec

/-- `PMULL2 v.1q, a.2d, b.2d` (`vmull_high_p64`): carry-less product of high 64-bit lanes. -/
def vmull_high_p64 (a b : V128) : V128 :=
  polynomialMult (V128.hi64 a).toBitVec (V128.hi64 b).toBitVec

/-- `PCLMULQDQ xmm1, xmm2, imm8` (`_mm_clmulepi64_si128`): bit 0 selects the
quadword of `a` and bit 4 selects the quadword of `b`; all other bits of `imm8`
are ignored by the architecture. -/
def clmulepi64 (a b : V128) (imm8 : UInt8) : V128 :=
  let src1 := if imm8.toBitVec.getLsbD 0 then (V128.hi64 a).toBitVec else (V128.lo64 a).toBitVec
  let src2 := if imm8.toBitVec.getLsbD 4 then (V128.hi64 b).toBitVec else (V128.lo64 b).toBitVec
  polynomialMult src1 src2

/-! ### Unaligned little-endian 64-bit and 128-bit memory loads -/

theorem usize_size_gt : 0x80000000 ≤ USize.size := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.size, h]

theorem usize_add_toNat (i : USize) (k : Nat) (h : i.toNat + k < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  have := usize_size_gt
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega)]
  exact Nat.mod_eq_of_lt h

/-- Little-endian 64-bit word assembled from eight bytes. -/
def word64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Unaligned little-endian 64-bit load at byte offset `i` (`LDR Xt` / `MOV r64, m64`,
or half of `LDR Qt` / `MOVDQU xmm, m128`). Proof arguments `hs` and `h` guarantee
`i.toNat + 8 ≤ a.size` and are erased at runtime. -/
def loadU64LE (a : @& ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) : UInt64 :=
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := usize_add_toNat i 7 (by omega)
  word64 (a.uget i (by omega)) (a.uget (i + 1) (by omega)) (a.uget (i + 2) (by omega))
    (a.uget (i + 3) (by omega)) (a.uget (i + 4) (by omega)) (a.uget (i + 5) (by omega))
    (a.uget (i + 6) (by omega)) (a.uget (i + 7) (by omega))

/-- Unaligned 128-bit vector load (`LDR Qt` / `vld1q_u8` / `_mm_loadu_si128`),
modeled as the pair of adjacent unaligned little-endian 64-bit loads. -/
def vld1q (a : @& ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 16 ≤ a.size) : V128 :=
  have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
  V128.ofHalves (loadU64LE a i hs (by omega)) (loadU64LE a (i + 8) hs (by omega))

end Model

end SimdModels
