/-
Quick agreement and throughput check of the scratch-buffer portable kernel
(`rawExtendXor`) against the register kernel. Not the benchmark protocol.
Usage: bench_xor
-/
import MemcpyCrc32c.Impl.PortableXor

open Crc32c

def mkBuf (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := 88172645463325252
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    b := b.push x.toUInt8
  return b

def viaXor (s : UInt32) (a : ByteArray) (off len : Nat) : UInt32 :=
  if h : a.size < USize.size ∧ off.toUSize.toNat + len.toUSize.toNat ≤ a.size ∧
      3344 ≤ len.toUSize.toNat then
    rawExtendXor s a h.1 off.toUSize len.toUSize h.2.1 h.2.2
  else 0xDEADBEEF

def viaReg (s : UInt32) (a : ByteArray) (off len : Nat) : UInt32 :=
  if h : off + len ≤ a.size then rawExtendPortable s a off len h else 0xDEADBEEF

def main : IO Unit := do
  let big := mkBuf ((1 <<< 20) + 64)
  let mut cases := 0
  -- every length across the first few chunk boundaries, then scattered large lengths
  for len in (List.range 300).map (· + 3344) ++ (List.range 200).map (fun i => 16384 + 1696 - 100 + i)
      ++ (List.range 120).map (fun i => 32768 + 1672 - 60 + i)
      ++ (List.range 400).map (fun i => 3344 + i * 2617) do
    for off in [0, 1, 3, 7, 8, 13] do
      let s : UInt32 := 0x9E3779B9 * (len.toUInt32 + off.toUInt32 + 1)
      if viaXor s big off len != viaReg s big off len then
        IO.eprintln s!"MISMATCH off={off} len={len}"; IO.Process.exit 1
      cases := cases + 1
  IO.println s!"scratch-buffer kernel agrees with the register kernel on {cases} cases"
  for n in [4096, 8192, 16384, 32768, 65536, 1 <<< 18, 1 <<< 20] do
    for (name, f) in [("register 4x  ", viaReg), ("scratch xor  ", viaXor)] do
      let reps := (1 <<< 28) / n
      let mut best : Float := 0
      for _ in [0:5] do
        let t0 ← IO.monoNanosNow
        let mut s : UInt32 := 1
        for _ in [0:reps] do s := f s big 0 n
        let t1 ← IO.monoNanosNow
        if s == 0xDEADBEEF then IO.println ""
        let g := (n * reps).toFloat / (t1 - t0).toFloat
        if g > best then best := g
      IO.println s!"{name} n={n}: {best} GB/s"
