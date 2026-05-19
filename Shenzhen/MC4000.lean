import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.IOEffects
import Shenzhen.Notation

namespace MC4000

@[reducible] def numXBusPins := 2
@[reducible] def XBus := Fin numXBusPins
@[reducible] def numSimpleIOPins := 2
@[reducible] def SimpleIO := Fin numSimpleIOPins

inductive InternalReg | acc -- Only one register
deriving Repr, Lean.ToExpr

end MC4000

namespace MC4000

/-- `IP m` is the type of an instruction pointer for an `MC4000` with `m` instructions.
  Chips can have zero instructions, so `IP m` is equivalent to `if m = 0 then Unit else Fin m`, but
  this way we get `Repr` for free and nicer pattern-matching. -/
inductive IP : Nat → Type
| none : IP 0
| ofFin : Fin m → IP m
deriving Repr

namespace IP

instance : ReprAtom (IP 0) where

def toFin (h : m ≠ 0) : IP m → Fin m
| .none => False.elim (h rfl)
| .ofFin x => x

def mk' (ofNonZero : (m : Nat) → m ≠ 0 → Fin m) {m} : IP m :=
  match m with
  | 0 => .none
  | k + 1 => .ofFin <| ofNonZero (k + 1) (by simp)

/-- `(0 : Fin m)` unless `m = 0` -/
def null : IP m :=
  .mk' fun _ h => ⟨0, Nat.zero_lt_of_ne_zero h⟩

instance : Inhabited (IP m) where
  default := .null

instance : Coe (Fin m) (IP m) := ⟨.ofFin⟩

end IP

/-- Represents the state during some instruction. While executing an instruction (possibly across multiple ticks, in the case that we block on XBus),
  all fields stay the same -/
structure InstructionState (numInstr : Nat) where
  acc : Integer
  cond : ConditionalState numInstr
  ip : IP numInstr
deriving Repr

/-! ## A note about simple I/O
  "At any given time, a simple I/O pin is either in input mode or output mode. Writing a value
  to a pin register will put the corresponding pin into output mode with the specified output value.
  Reading a value from a pin register will put the corresponding pin into input mode, clearing any
  previously set output value." (copied from the manual)

  This is the only effect that can change the state of a chip mid-instruction. -/

/-- Represents all the data that can be mutated within an instruction, i.e. from tick to tick. -/
structure TickState where
/-- The values being written out of each simple I/O pin. Reading
    from a pin sets this value to 0 (but the read value is just the max of all the other writers on this wire).
    See `effects`.

    This may change from one tick to another within an instruction.
    For example, this occurs in the instruction `mov p0 x0` if the chip was writing something
    out of `p0` before this instruction. -/
  simpleIOOut : Vector SimpleIOData numSimpleIOPins

abbrev Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

abbrev RegOrInt :=
  _root_.Instruction.RegOrInt InternalReg XBus SimpleIO

namespace InstructionState

instance {m} : ToString (InstructionState m) where
  toString
  | { acc, cond := c, ip } =>
    let condStr := match c.boolFlags with
      | (true, false) => "+"
      | (false, true) => "-"
      | (false, false) => "none"
      | (true, true) => "?both true?"
    s!"[acc = {acc}; ip = {repr ip}; \
    cond = {condStr}; \
    hasRun = {c.hasRun.toList.zipIdx.filter Prod.fst})"

def init (m) : InstructionState m :=
  { acc := 0,
    cond := ⟨Vector.replicate m false, false, false⟩,
    ip := .null }

instance : Inhabited (InstructionState m) :=
  ⟨init m⟩

@[inline, specialize]
def modifyAcc (f : Integer → Integer) : InstructionState m → InstructionState m :=
  fun state => { state with acc := f state.acc }

/-- Set `acc` to `f acc other`. -/
@[inline, specialize]
def modifyAcc' (f : Integer → Integer → Integer) (other : Integer) : InstructionState m → InstructionState m :=
  modifyAcc (f · other)

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline] def setCondIff (b : Bool) : InstructionState m → InstructionState m :=
  fun state => { state with cond := ⟨state.cond.hasRun, b, !b⟩ }

@[inline] def setHasRun (which : Fin m) (b : Bool) : InstructionState m → InstructionState m :=
  fun state => { state with cond := {
    state.cond with hasRun := state.cond.hasRun.set which b }
  }

@[inline] def setIP (new : IP m) : InstructionState m → InstructionState m :=
  ({ · with ip := new })

@[inline] def modifyIP (f : IP m → IP m) : InstructionState m → InstructionState m :=
  fun state => { state with ip := f state.ip }

end InstructionState

namespace TickState

@[inline] def setSimpleIOOut (i : SimpleIO) (val : SimpleIOData) : TickState → TickState :=
  fun state => { state with simpleIOOut := Vector.set state.simpleIOOut i val }

@[inline] def clearSimpleIOOut (i : SimpleIO) : TickState → TickState :=
  setSimpleIOOut i 0

end MC4000.TickState

open MC4000 in
structure MC4000 where
  /-- The number of instructions on the chip. -/
  {m : outParam Nat}
  flags : Vector ConditionalFlag m
  instrs : Vector (Instruction m) m
deriving Repr

namespace MC4000

section mk'
variable (flags : Array ConditionalFlag) (instrs : Array (_root_.Instruction Nat InternalReg XBus SimpleIO))

abbrev mk'.jmpLabelsInBounds : Bool :=
  instrs.all fun
    | .jmp dst => dst < instrs.size
    | _ => true

/-- A more convenient constructor for `MC4000` with default `by decide` proofs. -/
def mk' (flagsAndInstrs : Array (ConditionalFlag × _root_.Instruction Nat InternalReg XBus SimpleIO))
    (h : mk'.jmpLabelsInBounds flagsAndInstrs.unzip.snd := by decide) : MC4000 :=
  let m := flagsAndInstrs.size
  match h' : flagsAndInstrs.unzip with
  | (flags, instrs) =>
    let instrs' : Array (Instruction m) :=
      instrs.attach.map fun ⟨i, hi⟩ =>
        match i with
        | .jmp dst => .jmp <| Fin.mk dst <| by
            replace h' : instrs = flagsAndInstrs.unzip.snd := h' ▸ rfl
            simp only [mk'.jmpLabelsInBounds, Array.all_eq_true', ←h'] at h
            replace h := h (.jmp dst) hi
            simpa [decide_eq_true_eq, h'] using h
        | .nop => .nop | .not => .not
        | .slp x => .slp x | .slx x => .slx x
        | .mov x y => .mov x y | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .dgt x => .dgt x
        | .dst x y => .dst x y
        | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y
    have : flags = flagsAndInstrs.unzip.1 ∧ instrs = flagsAndInstrs.unzip.2 := ⟨h' ▸ rfl, h' ▸ rfl⟩
    @MC4000.mk m ⟨flags, by simp [this]; rfl⟩ ⟨instrs', by simp [instrs', this]; rfl⟩

end mk'

namespace State

@[reducible]
def Effects (m : Nat) : Type → Type :=
  StateT (InstructionState m) <| IOEffects XBus SimpleIO TickState

/-- Return an `IOEffects` within the greater monad -/
def ret {m α} (bfx : IOEffects XBus SimpleIO TickState α) : Effects m α :=
  fun is => bfx <&> (·, is)

/-- Calculate the effect of a single instruction, including tick effects. Does not
  update the instruction pointer at all. -/
def effects {m} (instr : Instruction m) : Effects m Unit := do
  match instr with
  -- Basic
  | .nop => return
  | .mov src dst =>
    let d ← readRegOrInt src
    match dst with
    | .null => return
    | .internal .acc => modify ({· with acc := d})
    | .simpleIO i =>
      let d := d.toSimpleIOData
      ret (.simpleIOWrite i (TickState.setSimpleIOOut i d) d pure)
    | .xBus x => ret (.xBusWrite x d pure)
  | .jmp _ => return -- the jump is taken care of elsewhere
  | .slp ri =>
    let d ← readRegOrInt ri
    match d.clampToNat with
    | 0 => return
    | k + 1 => ret <| .sleep (k + 1) (Nat.succ_ne_zero _) pure
  | .slx r => ret (.poll r pure)
  -- Arithmetic
  | .add ri => doArith ri (· + ·)
  | .sub ri => doArith ri (· - ·)
  | .mul ri => doArith ri (· * ·)
  | .not => modify (.modifyAcc Integer.not)
  | .dgt ri => doArith ri Integer.getDigit -- set `acc` to the `ri`th digit of `acc`
  | .dst ri₁ ri₂ =>
    -- set the `ri₁`th digit of `acc` to `ri₂`
    let digit ← readRegOrInt ri₁
    let num ← readRegOrInt ri₂
    modify (.modifyAcc (Integer.setDigit · digit num))
  -- Test (comparison)
  | .teq ri₁ ri₂ => doCmp ri₁ ri₂ (· == ·)
  | .tgt ri₁ ri₂ => doCmp ri₁ ri₂ (· > ·)
  | .tlt ri₁ ri₂ => doCmp ri₁ ri₂ (· < ·)
  | .tcp ri₁ ri₂ =>
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify fun state => { state with cond := ⟨state.cond.hasRun, d₁ < d₂, d₁ > d₂⟩ }
where
  readRegOrInt (ri : RegOrInt) : Effects m Integer := do
    match ri with
    | .int n => return n
    | .null => return 0
    | .internal .acc => return (←get).acc
    | .xBus x => do ret (.xBusRead x pure)
    | .simpleIO i => do ret (.simpleIORead i (TickState.clearSimpleIOOut i) (pure ∘ SimpleIOData.toInteger))

  doArith (ri : RegOrInt) (f : Integer → Integer → Integer) : Effects m Unit := do
    let d ← readRegOrInt ri
    modify (.modifyAcc' f d)

  doCmp ri₁ ri₂ f := do
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify (.setCondIff (f d₁ d₂))

/-- Find the index `i` of the next instruction at or after `start` that
  is enabled according to `flags[i]` and `cond`, looping back around from
  `i = m - 1` to `i = 0` if necessary. `none` if no such index exists.
  (We skip the `IP` constructor because it would always be a `Fin m`,
  as `m ≠ 0` by the existence of `start`.) -/
def nextIP {m} (flags : Vector ConditionalFlag m)
    (start : Fin m) (cond : ConditionalState m) : Option (Fin m) :=
  let foundOffset := Fin.find? fun offset =>
    let i := offset + start
    match flags[i] with
    | .none => true
    | .pos => cond.posEnabled
    | .neg => cond.negEnabled
    | .once => !cond.hasRun[i]
  foundOffset <&> (· + start)

/-- Advance the IP inside `StateM` to the location of the next currently enabled instruction.
  If impossible, stays on the current IP. Returns success (inside `StateM`). -/
def advanceIP {m} (flags : Vector ConditionalFlag m) : StateM (InstructionState m) Bool := do
  let state ← get
  let .ofFin ip := state.ip | return false
  let next := nextIP flags ip state.cond
  match next with
  | none => return false
  | some ip' =>
    modify <| InstructionState.setIP ip'
    return true
