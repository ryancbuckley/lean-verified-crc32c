/-
Quick agreement and throughput check of the scratch-buffer portable kernel
(`rawExtendXor`) against the register kernel. Not the benchmark protocol.
Usage: bench_xor
-/
import MemcpyCrc32c.Impl.PortableXor
import MemcpyCrc32c.Impl.Reference

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
  if h : a.size < USize.size ∧ off.toUSize.toNat + len.toUSize.toNat ≤ a.size then
    rawExtendPortableReg s a h.1 off.toUSize len.toUSize h.2
  else 0xDEADBEEF

/-- Differential check of the two trusted store bindings against their models,
on an unshared array (stored in place) and a shared one (stored into a copy,
leaving the original untouched). -/
def storeDiff : IO Nat := do
  let src := mkBuf 4096
  let mut x : UInt64 := 0x243F6A8885A308D3
  let mut cases := 0
  for size in [8, 9, 15, 16, 31, 32, 33, 40, 63, 64, 65, 200] do
    for i in [0:size] do
      x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
      let v0 := x; let v1 := x * 0x9E3779B97F4A7C15; let v2 := ~~~x; let v3 := x >>> 5
      let shared := src.extract i (i + size)
      let keep := shared.data.toList
      if h : i.toUSize.toNat + 8 ≤ shared.size then
        let want := SimdModels.Model.storeU64LE shared i.toUSize v0 h
        let fresh := src.extract i (i + size)
        if hf : i.toUSize.toNat + 8 ≤ fresh.size then
          if (SimdModels.storeU64LE fresh i.toUSize v0 hf).data.toList != want.data.toList then
            throw <| IO.userError s!"storeU64LE (in place) differs from its model: size={size} i={i}"
        if (SimdModels.storeU64LE shared i.toUSize v0 h).data.toList != want.data.toList then
          throw <| IO.userError s!"storeU64LE (copy) differs from its model: size={size} i={i}"
        cases := cases + 2
      if h : i.toUSize.toNat + 32 ≤ shared.size then
        let want := SimdModels.Model.storeU64x4LE shared i.toUSize v0 v1 v2 v3 h
        let fresh := src.extract i (i + size)
        if hf : i.toUSize.toNat + 32 ≤ fresh.size then
          if (SimdModels.storeU64x4LE fresh i.toUSize v0 v1 v2 v3 hf).data.toList
              != want.data.toList then
            throw <| IO.userError s!"storeU64x4LE (in place) differs from its model: size={size} i={i}"
        if (SimdModels.storeU64x4LE shared i.toUSize v0 v1 v2 v3 h).data.toList
            != want.data.toList then
          throw <| IO.userError s!"storeU64x4LE (copy) differs from its model: size={size} i={i}"
        cases := cases + 2
      if shared.data.toList != keep then
        throw <| IO.userError s!"a store modified a shared array: size={size} i={i}"
  return cases

def main : IO Unit := do
  let sc ← storeDiff
  IO.println s!"store bindings agree with their models on {sc} cases; shared arrays untouched"
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
