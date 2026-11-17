/-
Prototype check and timing of the Reed–Solomon kernel. Not a benchmark protocol.
Usage: bench_rs            (self-checks and timings)
       bench_rs vectors    (print parity for fixed inputs, for tests/rs_ref.py)
-/
import ReedSolomon.Impl.Kernel

open ReedSolomon

def mkBuf (n : Nat) (seed : UInt64 := 88172645463325252) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := seed
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    b := b.push x.toUInt8
  return b

def range (a b : Nat) : ByteArray := ⟨((List.range (b - a)).map (fun i => (a + i).toUInt8)).toArray⟩

def hex (b : ByteArray) : String :=
  String.join (b.data.toList.map fun x =>
    let d := "0123456789abcdef".toList
    String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

def encode (k m L : Nat) (data : ByteArray) : ByteArray :=
  interp (range 0 k) (range k (k + m)) L data

/-- Byte-at-a-time evaluation with the scalar field code only. -/
def slow (xs ys : ByteArray) (L : Nat) (data : ByteArray) : ByteArray :=
  tailBytes data (coeffs xs ys) ⟨Array.replicate (ys.size * L) 0⟩ L xs.size ys.size 0

def configs : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (2, 1, 31), (3, 2, 32), (4, 2, 33), (5, 3, 64), (10, 4, 100), (10, 4, 257),
   (17, 3, 96), (6, 6, 77), (20, 8, 40), (128, 127, 37), (200, 56, 64)]

def vectors : IO Unit := do
  for (k, m, L) in configs do
    let data := mkBuf (k * L)
    IO.println s!"{k} {m} {L} {hex data} {hex (encode k m L data)}"

def main (args : List String) : IO Unit := do
  if args == ["vectors"] then vectors; return
  -- agreement of the word kernel with the scalar code, and round trips
  let mut cases := 0
  let mut x : UInt64 := 0x243F6A8885A308D3
  for (k, m, L) in configs do
    let data := mkBuf (k * L)
    let par := encode k m L data
    if par.data != (slow (range 0 k) (range k (k + m)) L data).data then
      IO.eprintln s!"MISMATCH word/scalar k={k} m={m} L={L}"; IO.Process.exit 1
    let all := data ++ par
    for _ in [0:20] do
      -- choose k distinct survivors out of k+m by a random shuffle
      let mut idx := (List.range (k + m)).toArray
      for i in [0:k + m] do
        x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
        let j := i + (x.toNat % (k + m - i))
        let t := idx[i]!; idx := idx.set! i idx[j]!; idx := idx.set! j t
      let surv := idx.extract 0 k
      let lost := idx.extract k (k + m)
      let mut have_ := ByteArray.empty
      for s in surv do have_ := have_ ++ all.extract (s * L) (s * L + L)
      let mut want := ByteArray.empty
      for s in lost do want := want ++ all.extract (s * L) (s * L + L)
      let got := interp ⟨surv.map (·.toUInt8)⟩ ⟨lost.map (·.toUInt8)⟩ L have_
      if got.data != want.data then
        IO.eprintln s!"MISMATCH reconstruct k={k} m={m} L={L} surv={surv}"; IO.Process.exit 1
      cases := cases + 1
  IO.println s!"word kernel agrees with scalar code; {cases} random reconstructions recover the lost shards"
  for (k, m) in [(10, 4), (4, 2), (17, 3), (12, 8)] do
    for L in [4096, 65536, 65536 + 2080, 1 <<< 20, (1 <<< 20) + 2080] do
      let data := mkBuf (k * L)
      let reps := (1 <<< 28) / (k * L) + 1
      let c0 ← IO.monoNanosNow
      let coef := coeffs (range 0 k) (range k (k + m))
      let t0 ← IO.monoNanosNow
      IO.println s!"  coefficient set-up {k}+{m}: {(t0 - c0) / 1000} us [{coef.size}]"
      let mut acc : UInt8 := 0
      let mut out := zeros (m * L)
      for _ in [0:reps] do
        out := apply coef k m L data out
        acc := acc ^^^ out[0]!
      let t1 ← IO.monoNanosNow
      let gbs := (k * L * reps).toFloat / (t1 - t0).toFloat
      IO.println s!"encode {k}+{m} shard={L}: {gbs} GB/s of data ({gbs * m.toFloat / k.toFloat} GB/s of parity) [{acc}]"
