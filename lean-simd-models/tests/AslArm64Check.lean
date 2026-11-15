/-
Authoritative Arm ASL cross-check for `SimdModels.Arm64` (Phase 7):
compares `Arm64.decode` + `Arm64.execInstr` (`Arm64.step`) against full
architectural state-transition vectors produced from Arm's machine-readable ASL
by ASLp (`validation/aslp_arm64_vectors.py`).

Checks every component of `ArmState`:
- `pc`, `sp`, `nzcv` (`N, Z, C, V` flags)
- All 31 general-purpose registers `X0..X30` (catching upper-32 zeroing bugs)
- All 32 SIMD registers `V0..V31` (catching upper-64 zeroing / lane-clobber bugs)
- Every byte of the 384-byte `.rw` RAM window `[0x20000, 0x20180)` plus guard
  bytes `0x1FFFF` and `0x20180` (`none`).
-/
import SimdModels.Arm64

open SimdModels
open SimdModels.Arm64

private def memBase : UInt64 := 0x20000
private def memWords : Nat := 48
private def memBytes : Nat := memWords * 8

private def canaryX (i : Nat) : UInt64 :=
  0xA5A5000000000100 + i.toUInt64

private def canaryV (i : Nat) : V128 :=
  V128.ofHalves (0x5A5A000000000200 + i.toUInt64) (0xC3C3000000000300 + i.toUInt64)

private def canaryMemWord (k : Nat) : UInt64 :=
  0xD00D000000000000 + k.toUInt64 * 0x0102030405060708

private def canaryMem : Mem := fun addr =>
  if addr >= memBase && addr < memBase + memBytes.toUInt64 then
    let off := (addr - memBase).toNat
    let k := off / 8
    let sh := ((off % 8) * 8).toUInt64
    let b := ((canaryMemWord k) >>> sh).toUInt8
    some (.rw, b)
  else
    none

private def canaryState : ArmState :=
  let s0 : ArmState := { sp := 0x20080, pc := 0x10004124, mem := canaryMem }
  let s1 := (List.range 31).foldl (fun s i =>
    if h : i < 32 then s.setX ⟨i, h⟩ (canaryX i) else s) s0
  (List.range 32).foldl (fun s i =>
    if h : i < 32 then s.setV ⟨i, h⟩ (canaryV i) else s) s1

private def decodeNzcv (bits : Nat) : PState :=
  { n := ((bits >>> 3) &&& 1) == 1
  , z := ((bits >>> 2) &&& 1) == 1
  , c := ((bits >>> 1) &&& 1) == 1
  , v := (bits &&& 1) == 1 }

private def applyToken (s : ArmState) (tok : String) : Except String ArmState := do
  match tok.splitOn "=" with
  | [k, v] =>
    if k == "pc" then
      return { s with pc := v.toNat!.toUInt64 }
    else if k == "sp" then
      return { s with sp := v.toNat!.toUInt64 }
    else if k == "nzcv" then
      return { s with nzcv := decodeNzcv v.toNat! }
    else if k.startsWith "x" then
      let idx := (k.drop 1).toNat!
      if h : idx < 32 then
        return s.setX ⟨idx, h⟩ v.toNat!.toUInt64
      else throw s!"bad x reg: {tok}"
    else if k.startsWith "v" then
      let idx := (k.drop 1).toNat!
      match v.splitOn ":" with
      | [loS, hiS] =>
        if h : idx < 32 then
          return s.setV ⟨idx, h⟩ (V128.ofHalves loS.toNat!.toUInt64 hiS.toNat!.toUInt64)
        else throw s!"bad v reg: {tok}"
      | _ => throw s!"bad v value: {tok}"
    else if k.startsWith "m" then
      let mw := (k.drop 1).toNat!
      let addr := memBase + (mw * 8).toUInt64
      match s.mem.writeU64LE addr v.toNat!.toUInt64 with
      | some m' => return { s with mem := m' }
      | none => throw s!"mem write failed at word {mw}"
    else
      throw s!"unknown key in token: {tok}"
  | _ => throw s!"malformed token: {tok}"

private def applyTokens (s : ArmState) (part : String) : Except String ArmState :=
  let toks := (part.trimAscii.toString.splitOn " ").filter (fun t => !t.isEmpty)
  toks.foldlM applyToken s

private def checkLine (lineNo : Nat) (line : String) : Except String Unit := do
  match line.splitOn "|" with
  | [wStr, preStr, postStr] =>
    let w : UInt32 := wStr.trimAscii.toString.toNat!.toUInt32
    let pre ← applyTokens canaryState preStr
    let expected ← applyTokens pre postStr
    let code : UInt64 → Option UInt32 := fun addr => if addr == pre.pc then some w else none
    let some got := Arm64.step code pre
      | throw s!"line {lineNo} (w={w}): Arm64.step returned none (decode={repr (Arm64.decode w)})"
    if got.pc != expected.pc then
      throw s!"line {lineNo} (w={w}): PC mismatch got={got.pc} expected={expected.pc}"
    if got.sp != expected.sp then
      throw s!"line {lineNo} (w={w}): SP mismatch got={got.sp} expected={expected.sp}"
    if got.nzcv != expected.nzcv then
      throw s!"line {lineNo} (w={w}): NZCV mismatch got={repr got.nzcv} expected={repr expected.nzcv}"
    if got.regs != expected.regs then
      for i in List.range 31 do
        if h : i < 32 then
          let g := got.getX ⟨i, h⟩
          let e := expected.getX ⟨i, h⟩
          if g != e then
            throw s!"line {lineNo} (w={w}, ins={repr (Arm64.decode w)}): X{i} mismatch got={g} expected={e}"
    if got.simd != expected.simd then
      for i in List.range 32 do
        if h : i < 32 then
          let g := got.getV ⟨i, h⟩
          let e := expected.getV ⟨i, h⟩
          if g != e then
            throw s!"line {lineNo} (w={w}, ins={repr (Arm64.decode w)}): V{i} mismatch got=({V128.lo64 g},{V128.hi64 g}) expected=({V128.lo64 e},{V128.hi64 e})"
    for off in List.range memBytes do
      let addr := memBase + off.toUInt64
      if got.mem addr != expected.mem addr then
        throw s!"line {lineNo} (w={w}): mem[{addr}] mismatch got={repr (got.mem addr)} expected={repr (expected.mem addr)}"
    if got.mem (memBase - 1) != none || got.mem (memBase + memBytes.toUInt64) != none then
      throw s!"line {lineNo} (w={w}): out-of-bounds guard byte modified"
  | _ => throw s!"line {lineNo}: unparseable line: {line}"

partial def loop (h : IO.FS.Stream) (n : Nat) : IO Nat := do
  let line ← h.getLine
  if line.isEmpty then return n
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    loop h n
  else
    match checkLine (n + 1) trimmed with
    | .ok () => loop h (n + 1)
    | .error e => IO.eprintln s!"MISMATCH: {e}"; IO.Process.exit 1

def main : IO Unit := do
  let n ← loop (← IO.getStdin) 0
  IO.println s!"OK: SimdModels.Arm64.step agrees with Arm ASL (via ASLp) on all {n} full-state vectors"
