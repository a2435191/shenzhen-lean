module

public import Shenzhen.MC.Chip
public import Shenzhen.Integer

/-! # Defines the microcontrollers (MC4000, MC6000, and MC4000X ) -/

namespace MC.Chip
public section

/-- Just the `acc` register -/
inductive AccReg | acc

/-- Just the `acc` register -/
structure AccRegState where
  acc : Integer

instance : Registers AccReg AccRegState where
  acc := .acc
  read _ s := s.acc
  write _ d _ := ⟨d⟩
  modify _ f s := ⟨f s.acc⟩

instance : ToString AccRegState where
  toString s := s!"acc := {s.acc}"

@[expose] section
namespace MC4000

abbrev numXBusPins := 2
abbrev numSimpleIOPins := 2
abbrev InternalReg := AccReg
abbrev InternalRegState := AccRegState
abbrev blank : InternalRegState := ⟨0⟩
-- TODO this is so dumb that we have to repeat these
abbrev XBus := Fin 2
abbrev SimpleIO := Fin 2

end MC4000

-- TODO do other microcontrollers

open MC4000 in
def MC4000 : PartType :=
  { numXBusPins, numSimpleIOPins, InternalReg, InternalRegState, blank }
-- TODO make instance?
