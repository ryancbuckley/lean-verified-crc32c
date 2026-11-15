/-
Phase 7: AArch64 machine-code verification of the hardware CRC32C call graph
(7 functions, 1137 instructions), and its axiom audit.

Not imported by `MemcpyCrc32c` (the Phase 1-6 library): build it with
`lake build MemcpyCrc32c.Arm64`. `scripts/check_aarch64_mc.sh` checks that the
instruction words in `Arm64/Code.lean` are the bytes in the compiled objects.
-/
import MemcpyCrc32c.Arm64.ExtendHwRaw
import MemcpyCrc32c.Arm64.Copy
import MemcpyCrc32c.Arm64.CopySmall

open Crc32c.Arm64MC

/-- info: 'Crc32c.Arm64MC.combine3_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms combine3_mc_spec
/-- info: 'Crc32c.Arm64MC.combine6_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms combine6_mc_spec
/-- info: 'Crc32c.Arm64MC.hwLoop_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwLoop_mc_spec
/-- info: 'Crc32c.Arm64MC.hwFold6Loop_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwFold6Loop_mc_spec
/-- info: 'Crc32c.Arm64MC.hwFold6_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwFold6_mc_spec
/-- info: 'Crc32c.Arm64MC.rawExtendHwMulti_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExtendHwMulti_mc_spec
/-- info: 'Crc32c.Arm64MC.short_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms short_all
/-- info: 'Crc32c.Arm64MC.extendHwRaw_short_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHwRaw_short_mc_spec
/-- info: 'Crc32c.Arm64MC.extendHwRaw_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHwRaw_mc_spec
/-- info: 'Crc32c.Arm64MC.extendHwRaw_mc_eq_lean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHwRaw_mc_eq_lean

-- Hand-written copy routines (`cxx/leancrc32c_copy_arm64.S`, 31 + 48 instructions).
/-- info: 'Crc32c.Arm64MC.copyLarge_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copyLarge_mc_spec
/-- info: 'Crc32c.Arm64MC.copySmall_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copySmall_mc_spec
