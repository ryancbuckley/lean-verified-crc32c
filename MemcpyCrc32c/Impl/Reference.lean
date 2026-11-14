/-
The bitwise executable reference for CRC32C. No dependencies beyond Lean core,
so it can be compiled into native test and benchmark binaries. Proven equal to
the polynomial spec in `MemcpyCrc32c.Bitwise`.
-/

namespace Crc32c

/-- Advance the state by one zero bit: multiply by `X` modulo `G` (reflected). -/
@[inline] def stepBit (s : UInt32) : UInt32 :=
  (s >>> 1) ^^^ (if s &&& 1 = 1 then 0x82F63B78 else 0)

/-- Absorb one message byte. -/
@[inline] def stepByte (s : UInt32) (b : UInt8) : UInt32 :=
  stepBit <| stepBit <| stepBit <| stepBit <| stepBit <| stepBit <| stepBit <| stepBit
    (s ^^^ b.toUInt32)

/-- Unconditioned bitwise CRC over a list of bytes. -/
def rawExtend (s : UInt32) (bs : List UInt8) : UInt32 := bs.foldl stepByte s

/-- `absl::ExtendCrc32c`, bit at a time. The executable reference. -/
def extend (c : UInt32) (bs : ByteArray) : UInt32 :=
  rawExtend (c ^^^ 0xFFFFFFFF) bs.data.toList ^^^ 0xFFFFFFFF

/-- `absl::ComputeCrc32c`. -/
def crc32c (bs : ByteArray) : UInt32 := extend 0 bs

end Crc32c
