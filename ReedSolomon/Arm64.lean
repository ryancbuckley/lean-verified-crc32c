/-
AArch64 machine-code verification of the Reed–Solomon kernel `leanrs_apply`
(`cxx/leanrs_apply_arm64.S`, 117 instructions), and its axiom audit.

Not imported by `ReedSolomon`: build it with `lake build ReedSolomon.Arm64`.
`scripts/check_aarch64_mc.sh` checks that the instruction words in
`Arm64/Apply.lean` are the bytes of the assembled object.
-/
import ReedSolomon.Arm64.ApplySpec
import ReedSolomon.Tables

open ReedSolomon ReedSolomon.Arm64MC

/-- info: 'ReedSolomon.Arm64MC.apply_mc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms apply_mc_spec
/-- info: 'ReedSolomon.Arm64MC.apply_mc_shards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms apply_mc_shards
/-- info: 'ReedSolomon.apply_mc_rs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms apply_mc_rs
/-- info: 'ReedSolomon.ofByte_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ofByte_lagrange
/-- info: 'ReedSolomon.tables_isTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tables_isTable
