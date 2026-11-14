/-
Quick throughput check of the Lean portable path. Not the benchmark protocol;
just enough to steer optimization. Usage: bench_portable
-/
import MemcpyCrc32c.Impl.Portable

open Crc32c

def mkBuf (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := 88172645463325252
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    b := b.push x.toUInt8
  return b

def main : IO Unit := do
  -- agreement with the bitwise reference on a spread of sizes
  let small := mkBuf 5000
  for n in [0:700] do
    let a := small.extract (n % 7) (n % 7 + n * 7)
    let c : UInt32 := 0x12345678 + n.toUInt32
    if extendPortable c a != extend c a then
      IO.eprintln s!"MISMATCH n={a.size}"; IO.Process.exit 1
  IO.println "portable path agrees with the bitwise reference"
  for n in [16, 64, 256, 1024, 4096, 65536, 1048576, 67108864] do
    let a := mkBuf n
    let reps := max 3 (min 200000 (67108864 / n))
    let mut times : Array Nat := #[]
    let mut sink : UInt32 := 0
    for _ in [0:9] do
      let t0 ← IO.monoNanosNow
      for _ in [0:reps] do
        sink := extendPortable sink a
      let t1 ← IO.monoNanosNow
      times := times.push (t1 - t0)
    let med := (times.qsort (· < ·))[4]!
    let gbps := n.toFloat * reps.toFloat / med.toFloat
    IO.println s!"{n} bytes: {gbps} GB/s (median of 9)  [{sink}]"
