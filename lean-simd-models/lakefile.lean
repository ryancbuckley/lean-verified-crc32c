import Lake
open Lake DSL

package simdModels where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

/-- Every Lean-generated C file that uses a trusted binding must see the shim. -/
def shimArgs : Array String := #["-include", (__dir__ / "c" / "simd_shim.h").toString]

@[default_target]
lean_lib SimdModels where
  moreLeancArgs := shimArgs

lean_exe hw_diff where
  root := `tests.HwDiff
  moreLeancArgs := shimArgs
