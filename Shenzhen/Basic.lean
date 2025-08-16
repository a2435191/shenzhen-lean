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

structure Stmt (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x) where
  flag : CondFlag
  instr : Instruction Λ ρ ξ ι

/-- Whether a simple IO pin is in input or output mode. See the bottom
    of p. 18 (CSM_TD_1000198) of the manual. -/
inductive IOPinMode | input | output
deriving Repr

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
  ioPinModes : Vector IOPinMode numSimpleIOPins
  sleep : Sleep XBus
deriving Repr

namespace State

def init (m) [NeZero m] : State m :=
  { acc := 0,
    cond := ⟨false, false⟩,
    ip := 0,
    ioPinModes := #v[.input, .input],
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

@[inline]
def setIOPinMode (state : State m) (i : Fin numSimpleIOPins) (mode : IOPinMode) :=
  { state with ioPinModes := state.ioPinModes.set i mode }
end MC4000.State

open MC4000 in
structure MC4000 where
  {numInstr : Nat}
  instrs : Vector (Stmt (Fin numInstr) InternalReg XBus SimpleIO) numInstr
  state : State numInstr

-- for now, just MC4000s
structure Board where
  {numChips : Nat}
  chips : Vector MC4000 numChips
  ioConns : Fin numChips → SimpleIO → Array (Fin numChips × SimpleIO)
  xBusConns : Fin numChips → MC4000.XBus → Array (Fin numChips × MC4000.XBus)

/-- `PinStateM` wraps values of type `α` in a monad that
  records pin read and write actions, e.g. for computations
  within a chip with XBus (alternatively, simple IO) pins.
  - `ψ` is the type of *p*ins.
  - `δ` is the type of *d*ata (probably `Integer` or `IOData`). -/
inductive PinStateM (ψ : Type u) (δ : Type v) (α : Type w)
/-- Wrap a value in `PinStateM` without signaling the need for a read or write. -/
| pure : α → PinStateM ψ δ α
/-- `write pin d` represents some data `d` being written to
  pin `pin`. Note that `write` is a terminal action, so TODO -/
| write (pin : ψ) (d : δ)
/-- `read pin next` represents a computation delayed until a value `d`
  from pin `pin` can be read; then `next d` is the result of the computation. -/
| read (pin : ψ) (next : δ → PinStateM ψ δ α)
deriving Inhabited

instance [ToString ψ] [Repr α] : ToString (PinStateM ψ Integer α) :=
  ⟨toString⟩
where
  toString
  | .pure a => s!".pure {reprStr a}"
  | .write pin d => s!".write {pin} {reprStr d}"
  | .read pin next => s!".read {pin} (0 => {toString <| next 0})\n(1 => {toString <| next 1})\n(2 => {toString <| next 2})"

namespace PinStateM
def bind : PinStateM ψ δ α → (α → PinStateM ψ δ β) → PinStateM ψ δ β
| .pure a, f => f a
| .write pin d, _ => .write pin d
| .read pin next, f => .read pin (fun d => bind (next d) f)

instance : Monad (PinStateM ψ δ) where
  pure := PinStateM.pure
  bind := PinStateM.bind

instance : LawfulMonad (PinStateM ψ δ) :=
  .mk' _ (by intros; rfl) bind_assoc (id_map := id_map)
where
  bind_assoc {α β γ} (x : PinStateM ψ δ α) (f : α → PinStateM ψ δ β) (g : β → PinStateM ψ δ γ) :=
    match x with
    | .pure a => rfl
    | .read pin next => by
      simp [Bind.bind, bind]
      funext
      apply bind_assoc
    | .write pin d => by simp [Bind.bind, bind]
  id_map {α}
    | .pure a => rfl
    | .read pin next => by
      simp [Functor.map, bind]
      funext d
      apply id_map
    | .write pin d => by simp [Functor.map, bind]

end PinStateM

@[reducible] def MC4000.XBusPinStateM := PinStateM XBus Integer
structure MC4000.SimpleIOPinStateM (ι : Type u) (δ : Type v) (α : Type w) where
-- TODO

open MC4000 in
def doInstruction (instr : Instruction (Fin m) InternalReg XBus SimpleIO)
    (state : State m) (currentSimpleIOPinValues : Vector SimpleIOData numSimpleIOPins) : XBusPinStateM (State m) :=
  have : NeZero m := ⟨fun hn => Fin.elim0 (hn ▸ state.ip)⟩

  let notYetImplemented! {π} [Inhabited π] : π :=
    panic! s!"{repr instr} not yet implemented in `doInstruction`"

  -- TODO: put the pin modes part in a monad
  let readRI ri : XBusPinStateM Integer := match ri with
    | .int k => pure k
    | .reg .null => pure 0
    | .reg (.internal .acc) => pure state.acc
    | .reg (.io pin) => pure currentSimpleIOPinValues[pin] -- TODO : also set pin mode here
    | .reg (.xbus pin) => .read pin pure

  match instr with
  -- Basic instructions
  | .nop => pure state
  | .mov ri r => do
    let x ← readRI ri
    match r with
    | .null => return state
    | .internal .acc => return { state with acc := x }
    | .io pin => notYetImplemented!
    | .xbus pin => .write pin x
  | .jmp l =>
    return { state with ip := l }
  | .slp ri => do
    return { state with sleep := .slp (←readRI ri).n.toNatClampNeg }
  | .slx p =>
    return { state with sleep := .slx p }
  -- Arithmetic instructions
  | .add ri => do
    return state.modifyAcc Add.add (←readRI ri)
  -- Test instructions
  | .teq ri₁ ri₂ => do
    return state.setCondIff ((←readRI ri₁) == (←readRI ri₂))
  | _ => notYetImplemented!

#eval
  let y := doInstruction
    (.mov (.reg (.xbus 1)) (.xbus 0))
    { MC4000.State.init 3 with }
    #v[0, 0]
  y
