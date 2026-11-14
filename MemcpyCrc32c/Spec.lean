/-
The reference specification of CRC32C. Written for clarity, never for speed.
Everything else in the project is proven against the definitions in this file.

Conventions (confirmed against abseil's `crc32c.cc` and `crc32c_test.cc`):
a `crc32c_t` value is the fully conditioned, standard CRC32C. `ExtendCrc32c`
XORs with `0xFFFFFFFF` on the way in and on the way out, and
`ComputeCrc32c(buf) = ExtendCrc32c(crc32c_t{0}, buf)`.
-/
import MemcpyCrc32c.Poly

namespace Crc32c
open Polynomial

noncomputable section

/-- The message as a polynomial: the first byte is most significant, and within
a byte bit 0 is most significant (CRC32C is a reflected CRC). -/
def msgPoly : List UInt8 → (ZMod 2)[X]
  | [] => 0
  | b :: bs => polyR b.toBitVec * X ^ (8 * bs.length) + msgPoly bs

/-- The 32-bit word whose reflected view is `p`: bit `i` is the coefficient of `X^(31-i)`. -/
def bitsR (p : (ZMod 2)[X]) : BitVec 32 :=
  (BitVec.ofBoolListLE ((List.range 32).map fun i => decide (p.coeff (31 - i) = 1))).setWidth 32

namespace Spec

/-- Unconditioned CRC state update: `(s · X^(8n) + M · X^32) mod G`. -/
def rawExtend (s : UInt32) (bs : List UInt8) : UInt32 :=
  ⟨bitsR ((polyR s.toBitVec * X ^ (8 * bs.length) + msgPoly bs * X ^ 32) %ₘ G)⟩

/-- `absl::ExtendCrc32c`: extend the CRC32C `c` of some prefix by the bytes `bs`. -/
def extend (c : UInt32) (bs : ByteArray) : UInt32 :=
  rawExtend (c ^^^ 0xFFFFFFFF) bs.data.toList ^^^ 0xFFFFFFFF

/-- `absl::ComputeCrc32c`: the standard CRC32C of `bs`. -/
def crc32c (bs : ByteArray) : UInt32 := extend 0 bs

end Spec

end

end Crc32c
