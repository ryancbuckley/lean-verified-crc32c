/-
Differential checker: reads test cases with abseil's answers on stdin (see
tests/absl_gen.cc for the format) and compares them with the Lean functions.
Exits non-zero on the first mismatch.
-/
import MemcpyCrc32c.Impl.Arith
import MemcpyCrc32c.Impl.Portable
import MemcpyCrc32c.Impl.Hw

open Crc32c

def hexByte (b : UInt8) : UInt8 :=
  if b <= '9'.toNat.toUInt8 then b - '0'.toNat.toUInt8 else b - 'a'.toNat.toUInt8 + 10

def parseHex (s : String) : ByteArray := Id.run do
  if s == "-" then return ByteArray.empty
  let raw := s.toUTF8
  let n := raw.size / 2
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push ((hexByte raw[2 * i]! <<< 4) ||| hexByte raw[2 * i + 1]!)
  return out

def u32 (s : String) : UInt32 := s.toNat!.toUInt32

def check (line : String) : Except String Unit := do
  let fail (got : UInt32) (want : UInt32) : Except String Unit :=
    if got == want then pure () else throw s!"MISMATCH got {got} want {want}: {line.take 200}"
  match line.splitOn " " with
  | ["E", init, bytes, want] | ["M", init, bytes, want] =>
    let c := u32 init
    let bs := parseHex bytes
    let w := u32 want
    fail (extend c bs) w
    fail (extendPortable c bs) w
    fail (extendHw c bs) w
    if h : 16 ≤ bs.size then
      let off := c.toNat % 7
      let len := bs.size - off - (c.toNat / 7) % 7
      have hsub : off + len ≤ bs.size := by omega
      let s := c ^^^ 0xffffffff
      fail (rawExtendHw s bs off len hsub) (rawExtendPortable s bs off len hsub)
  | ["Z", c, n, want] => fail (extendZeroes (u32 c) n.toNat!) (u32 want)
  | ["C", a, b, n, want] => fail (concat (u32 a) (u32 b) n.toNat!) (u32 want)
  | ["P", a, b, n, want] => fail (removePrefix (u32 a) (u32 b) n.toNat!) (u32 want)
  | ["S", a, b, n, want] => fail (removeSuffix (u32 a) (u32 b) n.toNat!) (u32 want)
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
