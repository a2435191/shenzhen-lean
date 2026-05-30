module

public import Lean.Elab.Term.TermElabM
public import Shenzhen.Line

import Shenzhen.Instruction
import Shenzhen.MC4000
import Shenzhen.Compile

-- TODO: allow any alphanumeric + '_' labels, including reserved words
-- TODO: grab space immediately after comment '#'
-- TODO: allow any characters after comment, including reserved words
-- TODO: properly parse empty lines in `mc`
-- TDOO: add `expectedType`s

namespace MCParser

public section

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

end

open Lean Elab Meta Term

instance : MonadExceptOf Exception (Except Exception) where
  throw := .error
  tryCatch := .tryCatch

abbrev ParseM := Except Exception

def ParseM.throwErrorAt (stx : Syntax) (msg : MessageData) : ParseM α :=
  .error (.error stx msg)

def parseInt (stx : Syntax) : ParseM Integer := do
  let (isNeg, n) : Bool × Nat := ← match stx with
    | `(int| -$n) => return (true, n.getNat)
    | `(int| +$n)
    | `(int| $n:num) => return (false, n.getNat)
    | _ => throwUnsupportedSyntax
  let m := if isNeg then -(n : Int) else n
  if h₁ : (m > 999) then
    .throwErrorAt stx "Number too large"
  else if h₂ : (m < -999) then
    .throwErrorAt stx "Number too small"
  else
    return .ofInt m (Int.not_lt.mp h₁) (Int.not_lt.mp h₂)

open MC4000

def parseReg (stx : Syntax) : ParseM (Instruction.Reg InternalReg XBus SimpleIO) := do
  match stx with
  | `(reg|null) => return .null
  | `(reg|acc)  => return .internal .acc
  | `(reg|x0)   => return .xBus 0
  | `(reg|x1)   => return .xBus 1
  | `(reg|p0)   => return .simpleIO 0
  | `(reg|p1)   => return .simpleIO 1
  | `(reg|$_)   => .throwErrorAt stx "No such pin or register exists"

def parseRegOrInt : Syntax → ParseM (Instruction.RegOrInt InternalReg XBus SimpleIO)
| `(reg_or_int| $x:reg) => do return .reg (←parseReg x)
| `(reg_or_int| $x:int) => do return .int (←parseInt x)
| _ => throwUnsupportedSyntax

def parseInstr : Syntax → ParseM (_root_.Instruction String InternalReg XBus SimpleIO)
| `(shenzhen_mc_instr| nop) => return .nop
| `(shenzhen_mc_instr| not) => return .not
| `(shenzhen_mc_instr| mov $x $y) => return .mov (←parseRegOrInt x) (←parseReg y)
| `(shenzhen_mc_instr| jmp $l) => return .jmp (l.getId.toString false)
-- We don't call `elabReg` here because that produces an `Instruction.Reg`. We just want a `ξ`, which is `MC4000.XBus`.
| `(shenzhen_mc_instr| slx x0) => return .slx 0
| `(shenzhen_mc_instr| slx x1) => return .slx 1
| `(shenzhen_mc_instr| slx $r) => .throwErrorAt r "`slx` only works with XBus registers"
| `(shenzhen_mc_instr| slp $ri) => return .slp (←parseRegOrInt ri)
| `(shenzhen_mc_instr| add $ri) => return .add (←parseRegOrInt ri)
| `(shenzhen_mc_instr| sub $ri) => return .sub (←parseRegOrInt ri)
| `(shenzhen_mc_instr| mul $ri) => return .mul (←parseRegOrInt ri)
| `(shenzhen_mc_instr| dgt $ri) => return .dgt (←parseRegOrInt ri)
| `(shenzhen_mc_instr| dst $ri₁ $ri₂) => return .dst (←parseRegOrInt ri₁) (←parseRegOrInt ri₂)
| `(shenzhen_mc_instr| teq $ri₁ $ri₂) => return .teq (←parseRegOrInt ri₁) (←parseRegOrInt ri₂)
| `(shenzhen_mc_instr| tgt $ri₁ $ri₂) => return .tgt (←parseRegOrInt ri₁) (←parseRegOrInt ri₂)
| `(shenzhen_mc_instr| tlt $ri₁ $ri₂) => return .tlt (←parseRegOrInt ri₁) (←parseRegOrInt ri₂)
| `(shenzhen_mc_instr| tcp $ri₁ $ri₂) => return .tcp (←parseRegOrInt ri₁) (←parseRegOrInt ri₂)
| _ => throwUnsupportedSyntax

public def parseLine : Syntax → Except Exception MC4000.Line
| `(line| $(labelFull)? $(cond)? $(instr)? $(comment)?) => do
  let label := labelFull <&> fun
    | `(label| $l:ident :) => l.getId.toString false
    | _ => unreachable!
  let condition := (cond <&> fun
    | `(cond| +) => .pos
    | `(cond| -) => .neg
    | `(cond| @) => .once
    | _ => unreachable!).getD .none
  let instruction ← match instr with
    | none => pure none
    | some stx => some <$> parseInstr stx
  let comment := comment <&> fun
    | `(comment| # $s) => s.getId.toString false
    | _ => unreachable!

  return { label, condition, instruction, comment }
| _ => throwUnsupportedSyntax

public def elabLine : TermElab := fun stx _ =>
  match parseLine stx with
  | .error e => throw e
  | .ok line => return toExpr line
