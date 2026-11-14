/-
Authoritative Arm cross-check, step 2: compare the Lean models with vectors
produced from Arm's machine-readable ASL by ASLp (validation/aslp_vectors.py).
Reads the vectors on stdin; exits non-zero on the first mismatch.
-/
import SimdModels.Models

open SimdModels

def checkLine (line : String) : Except String Unit := do
  let bad (got : Nat) : Except String Unit := throw s!"MISMATCH model={got}: {line}"
  match line.splitOn " " with
  | ["crc32c_u8", c, v, r] =>
    let m := (Model.crc32c_u8 c.toNat!.toUInt32 v.toNat!.toUInt8).toNat
    if m != r.toNat! then bad m
  | ["crc32c_u16", c, v, r] =>
    let m := (Model.crc32c_u16 c.toNat!.toUInt32 v.toNat!.toUInt16).toNat
    if m != r.toNat! then bad m
  | ["crc32c_u32", c, v, r] =>
    let m := (Model.crc32c_u32 c.toNat!.toUInt32 v.toNat!.toUInt32).toNat
    if m != r.toNat! then bad m
  | ["crc32c_u64", c, v, r] =>
    let m := (Model.crc32c_u64 c.toNat!.toUInt32 v.toNat!.toUInt64).toNat
    if m != r.toNat! then bad m
  | ["pmull", a, b, lo, hi] =>
    let ml := (Model.clmulLo a.toNat!.toUInt64 b.toNat!.toUInt64).toNat
    let mh := (Model.clmulHi a.toNat!.toUInt64 b.toNat!.toUInt64).toNat
    if ml != lo.toNat! then bad ml
    if mh != hi.toNat! then bad mh
  | _ => throw s!"unparseable line: {line}"

partial def loop (h : IO.FS.Stream) (n : Nat) : IO Nat := do
  let line ← h.getLine
  if line.isEmpty then return n
  match checkLine line.trimAscii.toString with
  | .ok () => loop h (n + 1)
  | .error e => IO.eprintln e; IO.Process.exit 1

def main : IO Unit := do
  let n ← loop (← IO.getStdin) 0
  IO.println s!"OK: Lean models agree with Arm ASL (via ASLp) on {n} vectors"
