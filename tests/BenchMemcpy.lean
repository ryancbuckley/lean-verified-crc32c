/-
Quick throughput check of the Lean `memcpyCrc32c` paths. Not the benchmark
protocol. Compare with bench/absl_quick.cc on the same machine.
-/
import MemcpyCrc32c.Impl.Memcpy

open Crc32c

def mkBuf (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := 88172645463325252
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    b := b.push x.toUInt8
  return b

/-- `reps` copies of `src` into `dst`, chaining the CRC. Keeps `dst` unshared so the copy is in place. -/
def runHw (reps : Nat) (src : @& ByteArray) (dst : ByteArray) (c : UInt32) : ByteArray × UInt32 :=
  match reps with
  | 0 => (dst, c)
  | k + 1 =>
    if h : src.size ≤ dst.size then
      let (d, c') := memcpyCrc32cHw dst 0 src 0 src.size c (by omega) (by omega)
      runHw k src d c'
    else (dst, c)

def runPortable (reps : Nat) (src : @& ByteArray) (dst : ByteArray) (c : UInt32) : ByteArray × UInt32 :=
  match reps with
  | 0 => (dst, c)
  | k + 1 =>
    if h : src.size ≤ dst.size then
      let (d, c') := memcpyCrc32cPortable dst 0 src 0 src.size c (by omega) (by omega)
      runPortable k src d c'
    else (dst, c)

def main : IO Unit := do
  -- correctness spot check: copy is exact, CRC equals the bitwise reference
  let s := mkBuf 30000
  for k in [0:120] do
    let n := k * 251
    let sOff := k % 13
    let dOff := k % 7
    if h : sOff + n ≤ s.size ∧ dOff + n ≤ 31000 then
      let dst := ByteArray.mk (Array.replicate 31000 0x5a)
      have hd : dOff + n ≤ dst.size := by simp [dst, ByteArray.size]; omega
      let (d, c) := memcpyCrc32cHw dst dOff s sOff n 7 h.1 hd
      let (d2, c2) := memcpyCrc32cPortable dst dOff s sOff n 7 h.1 hd
      let want := extend 7 (s.extract sOff (sOff + n))
      if c != want || c2 != want || d.extract dOff (dOff + n) != s.extract sOff (sOff + n)
          || d != d2 || d.size != 31000 || d.extract 0 dOff != dst.extract 0 dOff
          || d.extract (dOff + n) 31000 != dst.extract (dOff + n) 31000 then
        IO.eprintln s!"MISMATCH n={n}"; IO.Process.exit 1
  IO.println "memcpyCrc32c: copies exact, CRCs agree with the bitwise reference"
  let warm := mkBuf 65536
  let (_, w) := runHw 6000 warm (ByteArray.mk (Array.replicate 65536 0)) 0
  if w == 0xDEADBEEF then IO.println ""
  for (name, isHw) in [("memcpyCrc32cHw", true), ("memcpyCrc32cPortable", false)] do
    for n in [16, 64, 256, 1024, 4096, 65536, 1048576, 67108864] do
      let src := mkBuf n
      let reps := max 3 (min 200000 (67108864 / n))
      let mut dst := ByteArray.mk (Array.replicate n 0)
      let mut times : Array Nat := #[]
      let mut sink : UInt32 := 0
      for _ in [0:9] do
        let t0 ← IO.monoNanosNow
        let (d, c) := if isHw then runHw reps src dst sink else runPortable reps src dst sink
        let t1 ← IO.monoNanosNow
        dst := d; sink := c
        times := times.push (t1 - t0)
      let med := (times.qsort (· < ·))[4]!
      IO.println s!"{name} {n} bytes: {n.toFloat * reps.toFloat / med.toFloat} GB/s  [{sink}]"
