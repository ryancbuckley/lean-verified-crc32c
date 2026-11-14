/-
Differential checker: reads test cases with abseil's answers on stdin (see
tests/absl_gen.cc for the format) and compares them with the Lean functions.
Exits non-zero on the first mismatch.
-/
import MemcpyCrc32c.Impl.Arith

open Crc32c

def hexVal (c : Char) : UInt8 :=
  if c.isDigit then (c.toNat - '0'.toNat).toUInt8 else (c.toNat - 'a'.toNat + 10).toUInt8

def parseHex (s : String) : ByteArray := Id.run do
  if s == "-" then return ByteArray.empty
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!)
  return out

def u32 (s : String) : UInt32 := s.toNat!.toUInt32

def check (line : String) : Except String Unit := do
  let fail (got : UInt32) (want : String) : Except String Unit :=
    if got == u32 want then pure () else throw s!"MISMATCH got {got}: {line.take 200}"
  match line.splitOn " " with
  | ["E", init, bytes, want] => fail (extend (u32 init) (parseHex bytes)) want
  | ["M", init, bytes, want] => fail (extend (u32 init) (parseHex bytes)) want
  | ["Z", c, n, want] => fail (extendZeroes (u32 c) n.toNat!) want
  | ["C", a, b, n, want] => fail (concat (u32 a) (u32 b) n.toNat!) want
  | ["P", a, b, n, want] => fail (removePrefix (u32 a) (u32 b) n.toNat!) want
  | ["S", a, b, n, want] => fail (removeSuffix (u32 a) (u32 b) n.toNat!) want
  | _ => throw s!"unparseable line: {line.take 200}"

partial def loop (h : IO.FS.Stream) (n : Nat) : IO Nat := do
  let line ← h.getLine
  if line.isEmpty then return n
  match check line.trimAscii.toString with
  | .ok () => loop h (n + 1)
  | .error e => IO.eprintln e; IO.Process.exit 1

def main : IO Unit := do
  let n ← loop (← IO.getStdin) 0
  IO.println s!"OK: {n} cases agree with abseil"
