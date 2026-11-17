/-
Untrusted generator for machine-code proof tables: reads 8-hex-digit A64
instruction words on stdin (one per line) and prints a Lean word array and a
binary-search function giving `Arm64.decode` of each word. The output is
checked in the proof by `checkWordsAux … = true := rfl`, so nothing here is
trusted.
Usage: lake env lean --run scripts/gen_arm64_insn_table.lean <wordsName> <insnName> < words.txt
-/
import SimdModels.Arm64
open SimdModels.Arm64

def hex64 (v : UInt64) : String := "0x" ++ String.ofList (Nat.toDigits 16 v.toNat)
def reg (r : RegIdx) : String := s!"r{r.val}"
def cnd (c : Fin 16) : String := s!"c{c.val}"
def bl (b : Bool) : String := toString b
def st : ShiftType → String | .lsl => ".lsl" | .lsr => ".lsr" | .asr => ".asr" | .ror => ".ror"
def lop : LogicOp → String | .andOp => ".andOp" | .orrOp => ".orrOp" | .eorOp => ".eorOp" | .andsOp => ".andsOp"
def mw : MovWideOp → String | .movn => ".movn" | .movz => ".movz" | .movk => ".movk"
def pm : PairMode → String | .postIndex => ".postIndex" | .signedOffset => ".signedOffset" | .preIndex => ".preIndex"
def ms : MemSize → String | .b8 => ".b8" | .h16 => ".h16" | .w32 => ".w32" | .x64 => ".x64"

def fmt : Instr → Option String
  | .b off => s!".b {hex64 off}"
  | .bCond c off => s!".bCond {cnd c} {hex64 off}"
  | .cbz sf nz rt off => s!".cbz {bl sf} {bl nz} {reg rt} {hex64 off}"
  | .ret rn => s!".ret {reg rn}"
  | .addSubImm sf sub fl rd rn imm => s!".addSubImm {bl sf} {bl sub} {bl fl} {reg rd} {reg rn} {hex64 imm}"
  | .logicImm sf op rd rn mask => s!".logicImm {bl sf} {lop op} {reg rd} {reg rn} {hex64 mask}"
  | .movWide sf op rd imm sh => s!".movWide {bl sf} {mw op} {reg rd} {imm.toNat} {sh}"
  | .ubfm sf rd rn immr imms => s!".ubfm {bl sf} {reg rd} {reg rn} {immr} {imms}"
  | .addSubReg sf sub fl s rd rn rm amt => s!".addSubReg {bl sf} {bl sub} {bl fl} {st s} {reg rd} {reg rn} {reg rm} {amt}"
  | .logicReg sf op s inv rd rn rm amt => s!".logicReg {bl sf} {lop op} {st s} {bl inv} {reg rd} {reg rn} {reg rm} {amt}"
  | .csel sf c rd rn rm => s!".csel {bl sf} {cnd c} {reg rd} {reg rn} {reg rm}"
  | .ldpGP sf m rt rt2 rn off => s!".ldpGP {bl sf} {pm m} {reg rt} {reg rt2} {reg rn} {hex64 off}"
  | .stpGP sf m rt rt2 rn off => s!".stpGP {bl sf} {pm m} {reg rt} {reg rt2} {reg rn} {hex64 off}"
  | .ldpQ m rt rt2 rn off => s!".ldpQ {pm m} {reg rt} {reg rt2} {reg rn} {hex64 off}"
  | .stpQ m rt rt2 rn off => s!".stpQ {pm m} {reg rt} {reg rt2} {reg rn} {hex64 off}"
  | .ldrUImm sz rt rn off => s!".ldrUImm {ms sz} {reg rt} {reg rn} {hex64 off}"
  | .strUImm sz rt rn off => s!".strUImm {ms sz} {reg rt} {reg rn} {hex64 off}"
  | .eorVec q rd rn rm => s!".eorVec {bl q} {reg rd} {reg rn} {reg rm}"
  | .eor3_16B rd rn rm ra => s!".eor3_16B {reg rd} {reg rn} {reg rm} {reg ra}"
  | .andVec16B rd rn rm => s!".andVec16B {reg rd} {reg rn} {reg rm}"
  | .ushr16B rd rn sh => s!".ushr16B {reg rd} {reg rn} {sh}"
  | .tbl1_16B rd rn rm => s!".tbl1_16B {reg rd} {reg rn} {reg rm}"
  | .movi16B rd imm => s!".movi16B {reg rd} {imm.toNat}"
  | _ => none

partial def tree (xs : Array String) (lo hi : Nat) (ind : String) : String :=
  if hi - lo == 1 then ind ++ xs[lo]! ++ "\n"
  else
    let mid := (lo + hi) / 2
    s!"{ind}if idx < {mid} then\n" ++ tree xs lo mid (ind ++ "  ") ++ s!"{ind}else\n" ++
      tree xs mid hi (ind ++ "  ")

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut words : Array UInt32 := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let t := line.trimAscii.toString
    if t.isEmpty then continue
    let some n := (t.toList.foldlM (fun acc c =>
        if c.isDigit then some (acc * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c ∧ c ≤ 'f' then some (acc * 16 + (c.toNat - 'a'.toNat + 10)) else none) 0 :
        Option Nat) | IO.eprintln s!"bad word {t}"; return 1
    words := words.push n.toUInt32
  let mut ins : Array String := #[]
  for w in words do
    match decode w >>= fmt with
    | some s => ins := ins.push s
    | none => IO.eprintln s!"cannot decode or format {w.toNat}"; return 1
  let wn := args[0]!
  let fn := args[1]!
  let hexw (w : UInt32) : String :=
    let d := Nat.toDigits 16 w.toNat
    "0x" ++ String.ofList (List.replicate (8 - d.length) '0' ++ d)
  let mut out := s!"def {wn} : Array UInt32 := #[\n"
  let n := words.size
  for i in [0:n] do
    out := out ++ (if i % 8 == 0 then "  " else " ") ++ hexw words[i]! ++
      (if i + 1 == n then "]\n" else if i % 8 == 7 then ",\n" else ",")
  out := out ++ s!"\ntheorem {wn}_size : {wn}.size = {n} := rfl\n\ndef {fn} (idx : Nat) : Arm64.Instr :=\n"
  out := out ++ tree ins 0 n "  "
  IO.print out
  return 0
