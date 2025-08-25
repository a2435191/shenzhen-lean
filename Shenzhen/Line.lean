import Shenzhen.Instruction
import Shenzhen.MC4000

variable (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x)

structure MCParser.Line where
  label : Option Λ
  condition : ConditionalFlag
  instruction : Option (Instruction Λ ρ ξ ι)
  comment : Option String
deriving Repr, Lean.ToExpr

abbrev MC4000.Line :=
  MCParser.Line String InternalReg XBus SimpleIO
