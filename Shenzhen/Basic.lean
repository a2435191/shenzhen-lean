import Shenzhen.Integer
import Shenzhen.Instruction
import Shenzhen.IOData

namespace MC4000

@[reducible] def numXBusPins := 2
@[reducible] def XBus := Fin numXBusPins
@[reducible] def numIOPins := 2
@[reducible] def IO := Fin numIOPins
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
structure State (numInstr : Nat) where
  acc : Integer
  cond : Condition
  ip : Fin numInstr
  ioPinModes : Vector IOPinMode numIOPins
deriving Repr

namespace State

instance [NeZero m] : Inhabited (State m) :=
  ⟨⟨0, .none, Fin.ofNat m 0, Vector.ofFn (fun _ => .input)⟩⟩

@[inline]
def modifyAcc (state : State m) (f : Integer → Integer → Integer) (other : Integer) :=
  { state with acc := f state.acc other }

/-- Set the `cond` internal register to be `pos` if `b` is `true` and `neg` otherwise. -/
@[inline]
def setCondIff (state : State m) (b : Bool) :=
  { state with cond := if b then .pos else .neg }

@[inline]
def incrementIp (state : State m) :=
  { state with ip := state.ip.succ' }

@[inline]
def setIOPinMode (state : State m) (i : Fin numIOPins) (mode : IOPinMode) :=
  { state with ioPinModes := state.ioPinModes.set i mode }
end MC4000.State

open MC4000 in
structure MC4000 where
  {numInstr : Nat}
  instrs : Vector (Stmt (Fin numInstr) InternalReg XBus IO) numInstr
  state : State numInstr

-- for now, just MC4000s
structure Board where
  {numChips : Nat}
  chips : Vector MC4000 numChips
  ioConns : Fin numChips → MC4000.IO → Array (Fin numChips × MC4000.IO)
  xBusConns : Fin numChips → MC4000.XBus → Array (Fin numChips × MC4000.XBus)

/-- `PinT` wraps values of type `α` in a monad that
  records pin read and write actions, e.g. for computations
  within a chip with XBus (alternatively, simple IO) pins.


  - `ψ` is the type of *p*ins.
  - `δ` is the type of *d*ata (probably `Integer` or `IOData`). -/
inductive PinT (ψ : Type u) (δ : Type v) (α : Type w)
/-- Wrap a value in `PinT` without signaling the need for a read or write. -/
| pure : α → PinT ψ δ α
-- /-- `write pin d next` represents some data `d` being written to
--   pin `pin`. Note that `write` is a terminal action, so TODO -/
| write (pin : ψ) (d : δ) --(next : α)
/-- `read pin next` represents a computation delayed until a value `d`
  from pin `pin` can be read; then `next d` is the result of the computation. -/
| read (pin : ψ) (next : δ → PinT ψ δ α)
deriving Inhabited

-- instance [ToString ψ] [Repr δ] [Repr α] : ToString (PinT ψ δ α) :=
--   ⟨toString⟩
-- where
--   toString
--   | .pure a => s!".pure {reprStr a}"
--   | .write pin d next => s!".write {pin} {reprStr d} ({reprStr next})"
--   | .read pin next => s!".read {pin} ⋯"

instance [ToString ψ] [Repr α] : ToString (PinT ψ Integer α) :=
  ⟨toString⟩
where
  toString
  | .pure a => s!".pure {reprStr a}"
  | .write pin d => s!".write {pin} {reprStr d}"
  | .read pin next => s!".read {pin} (0 => {toString <| next 0})\n(1 => {toString <| next 1})\n(2 => {toString <| next 2})"

namespace PinT
-- def bind (mx : PinT ψ δ α) (f : α → PinT ψ δ β) := match mx with
--   | .pure a => f a
--   | .read pin next => .read pin (fun d => bind (next d) f)
--   | .write pin d next => .write pin d (bind next f)

def bind : PinT ψ δ α → (α → PinT ψ δ β) → PinT ψ δ β
| .pure a, f => f a
| .write pin d, _ => .write pin d
| .read pin next, f => .read pin (fun d => bind (next d) f)

-- -- def PinT.map (f : α → β) : PinT ψ δ α → PinT ψ δ β
-- -- | .pure a => .pure (f a)
-- -- | .read pin next => .read pin (fun d => sorry)
-- -- | .write pin d next => sorry

instance : Monad (PinT ψ δ) where
  pure := PinT.pure
  bind := PinT.bind

instance : LawfulMonad (PinT ψ δ) :=
  .mk' _ (by intros; rfl) bind_assoc (id_map := id_map)
where
  bind_assoc {α β γ} (x : PinT ψ δ α) (f : α → PinT ψ δ β) (g : β → PinT ψ δ γ) :=
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

end PinT

@[reducible] def MC4000.XBusPinT := PinT MC4000.XBus Integer
@[reducible] def MC4000.IOPinT := PinT MC4000.IO IOData

open MC4000 in
def doInstruction (instr : Instruction (Fin m) InternalReg XBus IO) (state : State m) : XBusPinT (State m) :=
  have : NeZero m := ⟨fun hn => Fin.elim0 (hn ▸ state.ip)⟩

  let notYetImplemented! {π} [Inhabited π] (_ : Unit) : π :=
    panic! s!"{repr instr} not yet implemented in `doInstruction`"

  match instr with
  | .mov ri r => do
    let x : Integer ← match ri with
      | .int k => pure k
      | .reg .null => pure 0
      | .reg (.internal .acc) => pure state.acc
      | .reg (.io _) => notYetImplemented! () -- TODO
      | .reg (.xbus pin) => .read pin pure

    match r with
    | .null => pure state
    | .internal .acc => pure { state with acc := x }
    | .io _ => notYetImplemented! ()
    | .xbus pin => PinT.write pin x

  | _ => notYetImplemented! ()

#eval
  let y := doInstruction (m := 3)
    (.mov (.reg (.xbus 1)) (.xbus 0))
    { acc := 0, cond := .none, ip := 0, ioPinModes := #v[.input, .input] }
  y
