import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Instruction

import Lean.Elab.Command
import Lean.ToExpr

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


-- set_option linter.unusedVariables false in
-- open Lean in
-- instance instToExprPinStateM.{u, v, w, x, y}
--     {ξ : Type u} {ι : Type v} {δ : Type w} {ε : Type x} {α : Type y}
--     [ToExpr ξ] [ToExpr ι] [ToExpr δ] [ToExpr ε] [ToExpr α]
--     [ToLevel.{u}] [ToLevel.{v}] [ToLevel.{w}] [ToLevel.{x}] [ToLevel.{y}]
--     : ToExpr (PinStateM ξ ι δ ε α) where
--   toTypeExpr := mkConst ``PinStateM levels
--   toExpr := go
-- where
--   levels := [toLevel.{u}, toLevel.{v}, toLevel.{w}, toLevel.{x}, toLevel.{y}]
--   types := #[toTypeExpr ξ, toTypeExpr ι, toTypeExpr δ, toTypeExpr ε, toTypeExpr α]
--   mkCtor ctorName args :=
--     mkAppN (.const ctorName levels) (types ++ args)
--   go
--   | .pure a => mkCtor ``PinStateM.pure #[toExpr a]
--   | .writeXBus pin d => mkCtor ``PinStateM.writeXBus #[toExpr pin, toExpr d]
--   | .writeSimpleIO pin d => mkCtor ``PinStateM.writeSimpleIO #[toExpr pin, toExpr d]
--   | .readXBus pin next =>
--     let funExpr := sorry -- toExpr next
--     mkCtor ``PinStateM.readXBus #[toExpr pin, funExpr]
--   | .readSimpleIO pin next =>
--     let funExpr := Expr.fu -- toExpr next
--     mkCtor ``PinStateM.readSimpleIO #[toExpr pin, funExpr]

@[reducible] def MC4000.XBusPinStateM :=
  PinStateM XBus SimpleIO Integer SimpleIOData

section
open MC4000 Lean
deriving instance ToExpr for XBus
deriving instance ToExpr for SimpleIO
deriving instance ToExpr for ConditionalState
deriving instance ToExpr for Sleep
deriving instance ToExpr for State
end

instance [Repr α] : Repr (MC4000.XBusPinStateM α) where
  reprPrec := go
where go x : Nat → Std.Format := Repr.addAppParen <| .group <| .nestD <|
  match x with
  | .pure a => ".pure" ++ .line ++ reprArg a
  | .writeXBus pin d =>
    ".writeXBus" ++ .line ++ reprArg pin ++ .line ++ reprArg d
  | .writeSimpleIO pin d =>
    ".writeSimpleIO" ++ .line ++ reprArg pin ++ .line ++ reprArg d
  | .readXBus pin next =>
    ".readXBus" ++ .line ++ reprArg pin ++ .line ++ "fun 15 =>" ++ .line ++ (go (next 15) (eval_prec arg))
  | .readSimpleIO pin next =>
    ".readSimpleIO" ++ .line ++ reprArg pin ++ .line ++ "fun 15 =>" ++ .line ++ (go (next 15) (eval_prec arg))

open MC4000 in
def doInstruction (instr : Instruction (Fin m) InternalReg XBus SimpleIO)
    (state : State m) : XBusPinStateM (State m) :=
  have : NeZero m := ⟨fun hn => Fin.elim0 (hn ▸ state.ip)⟩

  let notYetImplemented! {π} [Inhabited π] : π :=
    panic! s!"{repr instr} not yet implemented in `doInstruction`"

  let readRI ri : XBusPinStateM Integer := match ri with
    | .int k => pure k
    | .reg .null => pure 0
    | .reg (.internal .acc) => pure state.acc
    | .reg (.io pin) => .readSimpleIO pin (pure ∘ SimpleIOData.toInteger)
    | .reg (.xbus pin) => .readXBus pin pure

  match instr with
  -- Basic instructions
  | .nop => pure state
  | .mov ri r => do
    let x ← readRI ri
    match r with
    | .null => return state
    | .internal .acc => return { state with acc := x }
    | .io pin => .writeSimpleIO pin x.toSimpleIOData
    | .xbus pin => .writeXBus pin x
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
  doInstruction
    (.add (.reg (.io 0)))
    { MC4000.State.init 3 with }
