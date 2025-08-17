import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Instruction

namespace MC4000

@[reducible] def numXBusPins := 2
@[reducible] def XBus := Fin numXBusPins
@[reducible] def numSimpleIOPins := 2
@[reducible] def SimpleIO := Fin numSimpleIOPins
inductive InternalReg | acc -- Only one register
deriving Repr
end MC4000

inductive CondFlag | none | pos | neg | once

@[always_inline]
def Fin.succ' : Fin n → Fin n
| ⟨k, lt⟩ => ⟨(k + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt lt)⟩

namespace MC4000

inductive Sleep (ξ : Type u)
| slp : Nat → Sleep ξ
| slx : ξ → Sleep ξ
deriving Repr

structure State (numInstr : Nat) where
  acc : Integer
  cond : ConditionalState
  ip : Fin numInstr
  sleep : Sleep XBus
deriving Repr

namespace State

def init (m) [NeZero m] : State m :=
  { acc := 0,
    cond := ⟨false, false⟩,
    ip := 0,
    sleep := .slp 0 }

instance [NeZero m] : Inhabited (State m) :=
  ⟨init m⟩

@[inline]
def modifyAcc (state : State m) (f : Integer → Integer → Integer) (other : Integer) :=
  { state with acc := f state.acc other }

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline]
def setCondIff (state : State m) (b : Bool) :=
  { state with cond := ⟨b, !b⟩ }

@[inline]
def incrementIp (state : State m) :=
  { state with ip := state.ip.succ' }

-- @[inline]
-- def setIOPinMode (state : State m) (i : Fin numSimpleIOPins) (mode : IOPinMode) :=
--   { state with ioPinModes := state.ioPinModes.set i mode }
end State

@[reducible]
def Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

end MC4000

open MC4000 in
structure MC4000 where
  /-- The number of instructions on the chip. -/
  {m : Nat}
  instrs : Vector (CondFlag × Instruction m) m
  state : State m

-- for now, just MC4000s
structure Board where
  {numChips : Nat}
  chips : Vector MC4000 numChips
  ioConns : Fin numChips → SimpleIO → Array (Fin numChips × MC4000.SimpleIO)
  xBusConns : Fin numChips → MC4000.XBus → Array (Fin numChips × MC4000.XBus)


inductive PinUseError (ξ ι : Type u)
| samePinReadTwice (pin : Pin ξ ι)
deriving Repr

def pinsReadByInstruction [BEq ξ] [BEq ι] : Instruction Λ ρ ξ ι → Except (PinUseError ξ ι) (List ξ × List ι)
| .nop | .jmp _ | .not | .slx _p =>
  .ok ([], []) -- TODO: check that this is correct for slx
| .mov ri _r
| .slp ri | .add ri | .sub ri | .mul ri | .dgt ri =>
  match ri.pin? with
  | none => .ok ([], [])
  | some (.xBus i) => .ok ([i], [])
  | some (.simpleIO i) => .ok ([], [i])
| .dst ri₁ ri₂ | .teq ri₁ ri₂ | .tgt ri₁ ri₂ | .tlt ri₁ ri₂ | .tcp ri₁ ri₂ => do
  match ri₁.pin?, ri₂.pin? with
  | some (.xBus a), some (.xBus b) =>
    if a == b then throw <| .samePinReadTwice (.xBus a)
  | some (.simpleIO a), some (.simpleIO b) =>
    if a == b then throw <| .samePinReadTwice (.simpleIO a)
  | _, _ => .ok ()

  let toListPair : Option (Pin ξ ι) → (List ξ × List ι)
    | none => ([], [])
    | some (.xBus j) => ([j], [])
    | some (.simpleIO j) => ([], [j])

  let (x₁, i₁) := toListPair ri₁.pin?
  let (x₂, i₂) := toListPair ri₂.pin?
  return (x₁ ++ x₂, i₁ ++ i₂)

def pinsWrittenByInstruction : Instruction Λ ρ ξ ι → Option (Pin ξ ι)
| .mov _ri r => r.pin?
| .nop | .jmp _ | .slp _ | .slx _
| .add _ | .sub _ | .mul _ | .not | .dgt _ | .dst ..
| .teq .. | .tgt .. | .tlt .. | .tcp .. => none

#eval
  let instr : MC4000.Instruction 9 := .tcp (.reg (.internal .acc)) (.reg (.internal .acc))
  let reads := pinsReadByInstruction instr
  let write? := pinsWrittenByInstruction instr
  (reads, write?)
