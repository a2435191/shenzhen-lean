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


/-- `PinStateM` wraps values of type `α` in a monad that
  records pin read and write actions within a chip with XBus and simple IO pins.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*O pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`).
  - `ε` is the type of data read over simple IO pins (probably `SimpleIOData`). -/
inductive PinStateM (ξ : Type u) (ι : Type v) (δ : Type w) (ε : Type x) (α : Type y)
/-- Wrap a value in `PinStateM` without signaling the need for a read or write. -/
| pure : α → PinStateM ξ ι δ ε α
/-- `writeXBus pin d` represents some data `d` being written to
  XBus pin `pin`. Note that `write` is a terminal action, so TODO -/
| writeXBus (pin : ξ) (d : δ)
/-- `writeSimpleIO pin d` represents some data `d` being written to
  simple IO pin `pin`. Note that `write` is a terminal action, so TODO -/
| writeSimpleIO (pin : ι) (d : ε)
/-- `readXBus pin next` represents a computation delayed until a value `d`
  from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| readXBus (pin : ξ) (next : δ → PinStateM ξ ι δ ε α)
/-- `readSimpleIO pin next` represents a computation delayed until the value `d`
  from simple IO pin `pin` is known; then `next d` is the result of the computation. -/
| readSimpleIO (pin : ι) (next : ε → PinStateM ξ ι δ ε α)
deriving Inhabited

-- inductive PinStateM' (ξ : Type u) (ι : Type v) (δ : Type w) (ε : Type x) (α : Type y)
-- | pure : α → PinStateM' ξ ι δ ε α
-- | writeXBus (pin : ξ) (d : δ)
-- | writeSimpleIO (pin : ι) (d : ε)
-- | readXBus (pin : ξ) (next : δ → PinStateM' ξ ι δ ε α)
-- | readSimpleIO (pin : ι) (next : ε → PinStateM' ξ ι δ ε α)
-- deriving Inhabited

namespace PinStateM
def bind : PinStateM ξ ι δ ε α → (α → PinStateM ξ ι δ ε β) → PinStateM ξ ι δ ε β
| .pure a, f => f a
| .writeXBus pin d, _ => .writeXBus pin d
| .writeSimpleIO pin d, _ => .writeSimpleIO pin d
| .readXBus pin next, f => .readXBus pin (fun d => bind (next d) f)
| .readSimpleIO pin next, f => .readSimpleIO pin (fun d => bind (next d) f)

instance : Monad (PinStateM ξ ι δ ε) where
  pure := PinStateM.pure
  bind := PinStateM.bind

instance : LawfulMonad (PinStateM ξ ι δ ε) :=
  .mk' _ (by intros; rfl) bind_assoc (id_map := id_map)
where
  bind_assoc {α β γ} (x : PinStateM ξ ι δ ε α) (f : α → PinStateM ξ ι δ ε β) (g : β → PinStateM ξ ι δ ε γ) := by
    cases x
    all_goals first
      | rfl
      | simp [Bind.bind, bind]
        funext
        apply bind_assoc
  id_map {α} (x) := by
    cases x
    all_goals first
      | rfl
      | simp [Functor.map, bind]
        funext d
        apply id_map
end PinStateM

@[reducible] def MC4000.PinStateM (m : Nat) :=
  _root_.PinStateM XBus SimpleIO (State m → Integer) (State m → SimpleIOData)

def MC4000.Instruction.toFn {m} (instr : Instruction m) (state : State m) : instr.FnType (State m) Integer :=
  let state := { state with ip :=
    match instr with
    | .jmp target => target
    | _ => state.ip.succ' }
  match instr with
  -- Basic instructions
  | .nop => state
  | .mov .. => fun
    | d, .internal .acc => { state with acc := d }
    | _, _ => state
  | .jmp _ => fun _ => state -- already set jump target above
  | .slp _ => fun { n, .. } => { state with sleep := .slp n.toNatClampNeg }
  | .slx _ => fun pin => { state with sleep := .slx pin }
  -- Arithmetic instructions
  | .add _ => state.modifyAcc Add.add
  | .sub _ => state.modifyAcc Sub.sub
  | .mul _ => state.modifyAcc Mul.mul
  | .not => { state with acc := ~~~state.acc }
  | .dgt _ => state.modifyAcc Integer.dgt
  | .dst .. => ({ state with acc := Integer.dst state.acc · · })
  -- Test instructions
  | .teq .. => (state.setCondIff <| · == ·)
  | .tgt .. => (state.setCondIff <| · > ·)
  | .tlt .. => (state.setCondIff <| · < ·)
  | .tcp .. => fun a b => { state with cond := ⟨a < b, a > b⟩ }

open MC4000 in
def instructionEffects {m} (instr : Instruction m) : PinStateM m (State m → State m) :=
  let readRI ri : MC4000.PinStateM m (State m → Integer) := match ri with
    | .int k => pure (fun _ => k)
    | .reg .null => pure (fun _ => 0)
    | .reg (.internal .acc) => pure State.acc
    | .reg (.simpleIO pin) => .readSimpleIO pin fun d => pure (SimpleIOData.toInteger ∘ d)
    | .reg (.xBus pin) => .readXBus pin pure

  let binFun ri f := do
    let d ← readRI ri
    return fun state => state.modifyAcc f (d state)

  let binRel ri₁ ri₂ r := do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state => state.setCondIff (r (fa state) (fb state))

  match instr with
  -- Basic instructions
  | .nop => pure id
  | .mov ri r => do
    let d ← readRI ri
    match r with
    | .null => return id
    | .internal .acc => return fun state => { state with acc := d state }
    | .simpleIO pin => .writeSimpleIO pin (Integer.toSimpleIOData ∘ d)
    | .xBus pin => .writeXBus pin d
  | .jmp l =>
    return ({ · with ip := l })
  | .slp ri => do
    let slpTime := Int16.toNatClampNeg ∘ Integer.n ∘ (←readRI ri)
    return fun state => { state with sleep := .slp (slpTime state)  }
  | .slx p =>
    return ({ · with sleep := .slx p })
  -- Arithmetic instructions
  | .add ri => inline (binFun ri Add.add)
  | .sub ri => inline (binFun ri Sub.sub)
  | .mul ri => inline (binFun ri Mul.mul)
  | .not =>
    return fun state => { state with acc := ~~~state.acc }
  | .dgt ri => inline (binFun ri Integer.dgt)
  | .dst ri₁ ri₂ => do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state => { state with acc := Integer.dst state.acc (fa state) (fb state) }
  -- Test instructions
  | .teq ri₁ ri₂ => inline (binRel ri₁ ri₂ BEq.beq)
  | .tgt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· > ·))
  | .tlt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· < ·))
  | .tcp ri₁ ri₂ => do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state =>
      let a := fa state
      let b := fb state
      { state with cond := ⟨a > b, a < b⟩ }
