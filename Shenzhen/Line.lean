module

public import Shenzhen.Instruction
public import Shenzhen.MC.Chips

public section

variable (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x)

structure MCParser.Line where
  label : Option Λ
  condition : ConditionalFlag
  instruction : Option (Instruction Λ ρ ξ ι)
  comment : Option String
deriving Repr

open MC.Chip.MC4000 in
@[expose]
abbrev MC4000.Line :=
  MCParser.Line String InternalReg XBus SimpleIO
-- TODO generalize this over all `MC.Chip` instances and use a typeclass
