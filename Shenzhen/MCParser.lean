import Shenzhen.Instruction
import Shenzhen.Basic
import Lean

-- TODO: allow any alphanumeric + '_' labels, including reserved words
-- TODO: grab space immediately after comment '#'
-- TODO: allow any characters after comment, including reserved words

structure MCParser.Line (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x) where
  label : Option Λ
  condition : ConditionalFlag
  instruction : Option (Instruction Λ ρ ξ ι)
  comment : Option String

abbrev MC4000.Line :=
  MCParser.Line String InternalReg XBus SimpleIO

namespace MCParser.Common

syntax int := (("-" <|> "+") noWs)? num
syntax reg := ident

syntax reg_or_int := reg <|> int

declare_syntax_cat shenzhen_mc_instr
syntax "nop" : shenzhen_mc_instr
syntax "not" : shenzhen_mc_instr
syntax "mov" reg_or_int ws reg : shenzhen_mc_instr
syntax "jmp" ident : shenzhen_mc_instr
syntax "slx" reg : shenzhen_mc_instr
syntax ("slp" <|> "add" <|> "sub" <|> "mul" <|> "dgt") reg_or_int : shenzhen_mc_instr
syntax ("dst" <|> "teq" <|> "tgt" <|> "tlt" <|> "tcp") reg_or_int ws reg_or_int : shenzhen_mc_instr

syntax cond := "+" <|> "-" <|> "@"
syntax comment := "#" ident
syntax label := ident ":"
syntax line := (label ppHardSpace)? (cond)? (shenzhen_mc_instr ppHardSpace)? (comment)?

end MCParser.Common

open Lean Elab Meta Term MCParser.Common

private def elabSimpleCtor (ctor : Name) (args : Array Expr) (expectedType? : Option Expr := none) : TermElabM Expr := do
  elabAppArgs (←mkConst' ctor) #[] (.expr <$> args) expectedType? false false

def MC4000.elabReg : TermElab := fun stx expectedType? => do
  let mkPin (xBus : Bool) (pin : Nat) : TermElabM Expr := do
    let ctor := if xBus then ``Instruction.Reg.xBus else ``Instruction.Reg.simpleIO
    let numPins := if xBus then ``numXBusPins else ``numSimpleIOPins
    let arg ← mkAppM ``Fin.ofNat #[←mkConst' numPins, mkNatLit pin]
    elabSimpleCtor ctor #[arg] expectedType?

  match stx with
  | `(reg|null) => elabSimpleCtor ``Instruction.Reg.null #[] expectedType?
  | `(reg|acc)  => elabSimpleCtor ``Instruction.Reg.internal #[←mkConst' ``InternalReg.acc] expectedType?
  | `(reg|x0)   => mkPin true 0
  | `(reg|x1)   => mkPin true 1
  | `(reg|p0)   => mkPin false 0
  | `(reg|p1)   => mkPin false 1
  | `(reg|$_)   => throwErrorAt stx "No such pin or register exists"

def elabInt (stx : Syntax) : MetaM Expr := do
  let (isNeg, n) : Bool × Nat := ← match stx with
    | `(int| -$n) => return (true, n.getNat)
    | `(int| +$n)
    | `(int| $n:num) => return (false, n.getNat)
    | _ => throwUnsupportedSyntax
  let m := if isNeg then -(n : Int) else n
  if (m > 999) then
    throwErrorAt stx "Number too large"
  if (m < -999) then
    throwErrorAt stx "Number too small"
  let mExpr ← mkAppM ``Int16.ofInt #[mkIntLit m]
  let mkInt16Lit (n : Int16) :=
    mkAppM ``Int16.ofInt #[mkIntLit n.toInt]
  let mkDecideLEProof (x y : Expr) := do
    mkDecideProof (←mkAppM ``LE.le #[x, y])

  mkAppM ``Integer.mk #[mExpr,
    ←mkDecideLEProof mExpr (←mkInt16Lit 999),
    ←mkDecideLEProof (←mkInt16Lit (-999)) mExpr]

def MC4000.elabRegOrInt : TermElab
| `(reg_or_int| $x:reg), _ => do
  let reg ← MC4000.elabReg x none
  elabSimpleCtor ``Instruction.RegOrInt.reg #[reg]
| `(reg_or_int| $x:int), _ => do
  let int ← elabInt x
  elabSimpleCtor ``Instruction.RegOrInt.int #[int]
| _, _ => throwUnsupportedSyntax

def instrSyntaxToName? : Syntax → Option Name
| `(shenzhen_mc_instr| nop)       => ``Instruction.nop
| `(shenzhen_mc_instr| not)       => ``Instruction.not
| `(shenzhen_mc_instr| mov $_ $_) => ``Instruction.mov
| `(shenzhen_mc_instr| jmp $_)    => ``Instruction.jmp
| `(shenzhen_mc_instr| slx $_)    => ``Instruction.slx
| `(shenzhen_mc_instr| slp $_)    => ``Instruction.slp
| `(shenzhen_mc_instr| add $_)    => ``Instruction.add
| `(shenzhen_mc_instr| sub $_)    => ``Instruction.sub
| `(shenzhen_mc_instr| mul $_)    => ``Instruction.mul
| `(shenzhen_mc_instr| dgt $_)    => ``Instruction.dgt
| `(shenzhen_mc_instr| dst $_ $_) => ``Instruction.dst
| `(shenzhen_mc_instr| teq $_ $_) => ``Instruction.teq
| `(shenzhen_mc_instr| tgt $_ $_) => ``Instruction.tgt
| `(shenzhen_mc_instr| tlt $_ $_) => ``Instruction.tlt
| `(shenzhen_mc_instr| tcp $_ $_) => ``Instruction.tcp
| _ => none

def MC4000.elabInstr : TermElab := fun stx _ => do
  if let some ctor := instrSyntaxToName? stx then
    match stx with
    | `(shenzhen_mc_instr| nop)
    | `(shenzhen_mc_instr| not)           => elabSimpleCtor ctor #[]
    | `(shenzhen_mc_instr| mov $x $y)     => elabSimpleCtor ctor #[←elabRegOrInt x none, ←elabReg y none]
    | `(shenzhen_mc_instr| jmp $l)        => elabSimpleCtor ctor #[mkStrLit (l.getId.toString false)]
    | `(shenzhen_mc_instr| slx $p)        => elabSimpleCtor ctor #[←elabReg p none]
    | `(shenzhen_mc_instr| slp $ri)
    | `(shenzhen_mc_instr| add $ri)
    | `(shenzhen_mc_instr| sub $ri)
    | `(shenzhen_mc_instr| mul $ri)
    | `(shenzhen_mc_instr| dgt $ri)       => elabSimpleCtor ctor #[←elabRegOrInt ri none]
    | `(shenzhen_mc_instr| dst $ri₁ $ri₂)
    | `(shenzhen_mc_instr| teq $ri₁ $ri₂)
    | `(shenzhen_mc_instr| tgt $ri₁ $ri₂)
    | `(shenzhen_mc_instr| tlt $ri₁ $ri₂)
    | `(shenzhen_mc_instr| tcp $ri₁ $ri₂) => elabSimpleCtor ctor #[←elabRegOrInt ri₁ none, ←elabRegOrInt ri₂ none]
    | _ => unreachable!
  else throwUnsupportedSyntax

def MC4000.elabLine : TermElab := fun stx _ => do
  match stx with
  | `(line| $(labelFull)? $(cond)? $(instr)? $(comment)?) =>
    let labelString := labelFull <&> fun
      | `(label| $l:ident :) => l.getId.toString false
      | _ => unreachable!
    let cond := (cond <&> fun
      | `(cond| +) => ``ConditionalFlag.pos
      | `(cond| -) => ``ConditionalFlag.neg
      | `(cond| @) => ``ConditionalFlag.once
      | _ => unreachable!).getD ``ConditionalFlag.none
    let instr ← match instr with
      | none => elabSimpleCtor ``Option.none #[]
      | some stx => elabSimpleCtor ``Option.some #[←MC4000.elabInstr stx none]
    let comment := comment <&> fun
      | `(comment| # $s) => s.getId.toString false
      | _ => unreachable!

    let string?ToExpr : Option String → TermElabM Expr
      | none => elabSimpleCtor ``Option.none #[]
      | some s => elabSimpleCtor ``Option.some #[mkStrLit s]

    elabSimpleCtor ``MCParser.Line.mk
      #[←string?ToExpr labelString, ←mkConst' cond, instr, ←string?ToExpr comment]
      (expectedType? := ←mkConst' ``MC4000.Line)
  | _ => unreachable!

-- elab "test_elabReg " e:reg : term => MC4000.elabReg e none
-- elab "test_elabInt " e:int : term => elabInt e
-- elab "test_elabRegOrInt " e:reg_or_int : term => MC4000.elabRegOrInt e none
-- elab "test_elabInstr " e:shenzhen_mc_instr : term => MC4000.elabInstr e none
elab "line(" e:line ")" : term => MC4000.elabLine e none

-- #check test_elabReg null
-- #eval test_elabInt -999
-- #check test_elabRegOrInt 3
-- #check test_elabInstr mov 0x0 acc
-- #check test_elabInstr tlt 999 p0
#reduce line(xlb0l: @mov p0 acc #a)
