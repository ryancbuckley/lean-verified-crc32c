/-
QUARANTINE: lemmas in this directory are proven with `bv_decide`, which relies
on the axiom `Lean.ofReduceBool` (it trusts the Lean compiler to run the
verified SAT-certificate checker). Only fixed-width word identities live here:
no spec, no polynomial reasoning. Anything that imports this file may depend
on `Lean.ofReduceBool`; the phase reports list which headline theorems do.
-/
import MemcpyCrc32c.Impl.Portable
import Std.Tactic.BVDecide

namespace Crc32c.BvDecide

/-- The byte fields of a little-endian word do not overlap, so OR is XOR. -/
theorem word64_eq_xor (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    word64 b0 b1 b2 b3 b4 b5 b6 b7 =
      b0.toUInt64 ^^^ (b1.toUInt64 <<< 8) ^^^ (b2.toUInt64 <<< 16) ^^^ (b3.toUInt64 <<< 24) ^^^
        (b4.toUInt64 <<< 32) ^^^ (b5.toUInt64 <<< 40) ^^^ (b6.toUInt64 <<< 48) ^^^
        (b7.toUInt64 <<< 56) := by
  unfold word64; bv_decide

/-- A word is the little-endian combination of its own bytes. -/
theorem word64_bytes (w : UInt64) :
    word64 w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8
      (w >>> 32).toUInt8 (w >>> 40).toUInt8 (w >>> 48).toUInt8 (w >>> 56).toUInt8 = w := by
  unfold word64; bv_decide

/-- Shifting left by 24 keeps only the low byte. -/
theorem shl24_eq_lowByte (s : UInt32) : s <<< 24 = s.toUInt8.toUInt32 <<< 24 := by
  bv_decide

end Crc32c.BvDecide
