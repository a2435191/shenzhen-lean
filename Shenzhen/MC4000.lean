import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.BlockingEffects
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

/-- The instruction pointer for an `MC4000` with `m` instructions. -/
abbrev IP (m) := Option (Fin m)

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
    s!"[acc = {acc}; ip = {ip}; \
    cond = {condStr}; \
    hasRun = {c.hasRun.toList.zipIdx.filter Prod.fst})"

def init (m) : InstructionState m :=
  { acc := 0,
    cond := ⟨Vector.replicate m false, false, false⟩,
    ip := if h : m = 0 then none else some ⟨0, Nat.zero_lt_of_ne_zero h⟩ }

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

end TickState

namespace IP

/-- Update the instruction pointer to its immediate successor,
  or `0` if the current IP is `none` and `m > 0`. -/
def succ : IP m → IP m
| none => if h : m > 0 then some ⟨0, h⟩ else none
| some i => i.succ'

/-- Update the instruction pointer to that of the next instruction,
  ignoring `state.sleep` and `+`/`-`/`@` conditionals. That is,
  `jmp` instructions map to the instruction's label, and all others
  just perform `succ`. -/
def next : Instruction m → IP m → IP m
| .jmp l => fun _ => l
| _ => succ

/-- Consider a chip with `m` conditional flags in the source (including `.none`) and
  the current conditional state `cond`. `currOrNextEnabled flags cond curr`
  returns the first (if one exists) instruction pointer `j ≥ curr` such that `j` is enabled under `cond` and `flags[j]`.  -/
def currOrNextEnabled (flags : Vector ConditionalFlag m) (cond : ConditionalState m) (curr : IP m) : IP m :=
  let instrEnabled j := flags[j].isEnabled cond j
  match curr with
  | none => Fin.find? instrEnabled
  | some ip =>
    if instrEnabled ip then some ip
    else Fin.nextFinIdx? ip instrEnabled

end MC4000.IP

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
def InstructionEffects (m : Nat) : Type → Type :=
  StateT (InstructionState m) <| BlockingEffects XBus SimpleIO

/-- Return a `BlockingEffects` within the greater monad -/
def ret {m α} (bfx : BlockingEffects XBus SimpleIO α) : InstructionEffects m α :=
  fun is => bfx <&> (·, is)

/-- Calculate the effect of a single instruction. Does update the instruction pointer.
  Does *not* account for the tick effects (TODO, see `TickState`)  -/
def instructionEffects {m} (instr : Instruction m) : InstructionEffects m Unit := do
  match instr with
  -- Basic
  | .nop => return
  | .mov src dst =>
    let d ← readRegOrInt src
    match dst with
    | .null => return
    | .internal .acc => modify ({· with acc := d})
    | .simpleIO i => ret (.simpleIOWrite i d.toSimpleIOData pure)
    | .xBus x => ret (.xBusWrite x d pure)
  | .jmp _ => return -- the jump is taken care of elsewhere
  | .slp ri =>
    let d ← readRegOrInt ri
    match d.clampToNat with
    | 0 => return
    | k + 1 => ret <| .sleep (k + 1) (by simp) pure
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
  readRegOrInt (ri : RegOrInt) : InstructionEffects m Integer := do
    match ri with
    | .int n => return n
    | .null => return 0
    | .internal .acc => return (←get).acc
    | .xBus x => do ret (.xBusRead x pure)
    | .simpleIO i => do ret (.simpleIORead i (pure ∘ SimpleIOData.toInteger))

  doArith (ri : RegOrInt) (f : Integer → Integer → Integer) : InstructionEffects m Unit := do
    let d ← readRegOrInt ri
    modify (.modifyAcc' f d)

  doCmp ri₁ ri₂ f := do
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify (.setCondIff (f d₁ d₂))
