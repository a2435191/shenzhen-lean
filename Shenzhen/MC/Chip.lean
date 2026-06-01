module

public import Lean.ToExpr

public import Shenzhen.Conns
public import Shenzhen.Instruction
public import Shenzhen.Integer
public import Shenzhen.IOEffects
public import Shenzhen.MC.IP

import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.Notation

import Batteries.Data.Fin.Basic

/-! # The interface for the MC4000, MC4000X, and MC6000 microcontrollers -/
-- TODO at some point add MC4010 math coprocessor. Not sure if that should use this interface though

public section -- TODO tighten
namespace MC

/-- `Registers ρ σ` is the interface for an implentation of internal registers for a chip type,
  where a value of `ρ` indicates a specific register, and `σ` holds the state of the registers.  -/
class Registers (ρ : outParam Type) (σ : Type) where
  /-- Which register is `acc`? -/
  acc : ρ
  read : ρ → σ → Integer
  write : ρ → Integer → σ → σ
  modify : ρ → (Integer → Integer) → σ → σ := fun which f s =>
    let d := read which s
    write which (f d) s
-- deriving Inhabited

-- TODO `deriving` instance causes a warning on Lean 4.30
instance [Inhabited ρ] : Inhabited (Registers ρ σ) where
  default := {
    acc := default,
    read _ _ := 0,
    write _ _ := id }

/-- Represents the state during some instruction. While executing an instruction (possibly across multiple, in the case that we block on XBus),
  all fields stay the same.

  `σ` is the type of internal registers (`acc` and `dat` or just `acc` alone). -/
structure InstructionState (σ : Type) (numInstr : Nat) where
  registers : σ
  cond : ConditionalState numInstr
  ip : IP numInstr
deriving Repr, Inhabited

-- TDOO maybe make this a typeclass
/-- The type of some chip, so just the metadata associated with every kind of MCxxxx product.
  Doesn't include per-chip information like the instructions or state.
  `ρ` is the type of *which* register (e.g. `acc` vs. `dat`); `σ` is the type of the entire register state. -/
public class PartType (numXBusPins numSimpleIOPins : outParam ℕ) (ρ σ : outParam Type)
    [Registers ρ σ] [ToString σ]
-- deriving Inhabited

variable [Registers ρ σ] [ToString σ]

namespace PartType

@[reducible, expose] def XBus [PartType numXBusPins numSimpleIOPins ρ σ] :=
  Fin numXBusPins
@[reducible, expose] def SimpleIO [PartType numXBusPins numSimpleIOPins ρ σ] :=
  Fin numSimpleIOPins
@[reducible, expose] def InstructionState [PartType numXBusPins numSimpleIOPins ρ σ] (m : ℕ) :=
  MC.InstructionState σ m

-- TODO: again, `deriving` instance doesn't work
instance : Inhabited (PartType numXBusPins numSimpleIOPins ρ σ) where
  default := ⟨⟩

end PartType

/-! ## A note about simple I/O
  "At any given time, a simple I/O pin is either in input mode or output mode. Writing a value
  to a pin register will put the corresponding pin into output mode with the specified output value.
  Reading a value from a pin register will put the corresponding pin into input mode, clearing any
  previously set output value." (copied from the manual)

  This and XBus writes (see below) are the only effects that can change the state of a chip mid-instruction. -/

open PartType

@[expose]
abbrev Instruction (numInstr : Nat) [inst : PartType numXBusPins numSimpleIOPins ρ σ] :=
  _root_.Instruction (Fin numInstr) XBus SimpleIO

@[expose]
abbrev RegOrInt [inst : PartType numXBusPins numSimpleIOPins ρ σ] :=
  _root_.Instruction.RegOrInt ρ XBus SimpleIO

namespace InstructionState

instance [ToString σ] {m} : ToString (InstructionState σ m) where
  toString
  | { registers, cond := c, ip } =>
    let condStr := match c.boolFlags with
      | (true, false) => "+"
      | (false, true) => "-"
      | (false, false) => "none"
      | (true, true) => "?both true?"
    s!"[registers = {registers}; ip = {repr ip}; \
    cond = {condStr}; \
    hasRun = {c.hasRun.toList.zipIdx.filter Prod.fst})"

-- TODO
-- instance : Inhabited (InstructionState m) :=
--   ⟨blank m⟩

-- TODO move this stuff to its own state file, with InstructionState stuff above

@[inline, specialize]
def modifyAcc [inst : Registers ρ σ] (f : Integer → Integer) : InstructionState σ m → InstructionState σ m :=
  fun state => { state with registers := Registers.modify inst.acc f state.registers }

/-- Set `acc` to `f acc other`. -/
@[inline, specialize]
def modifyAcc' [Registers ρ σ] (f : Integer → Integer → Integer) (other : Integer) : InstructionState σ m → InstructionState σ m :=
  modifyAcc (f · other)

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline] def setCondIff (b : Bool) : InstructionState σ m → InstructionState σ m :=
  fun state => { state with cond := ⟨state.cond.hasRun, b, !b⟩ }

@[inline] def setHasRun (which : Fin m) (b : Bool) : InstructionState σ m → InstructionState σ m :=
  fun state => { state with cond := {
    state.cond with hasRun := state.cond.hasRun.set which b }
  }

@[inline] def setIP (new : IP m) : InstructionState σ m → InstructionState σ m :=
  ({ · with ip := new })

@[inline] def modifyIP (f : IP m → IP m) : InstructionState σ m → InstructionState σ m :=
  fun state => { state with ip := f state.ip }

end InstructionState

-- TODO: consider parametrizing `Chip` on `τ`, so `MC4000 := Chip MC4000.PartType` or something
-- TODO: consider also parametrizing it on `m`
open PartType in
public structure Chip where
  /-- The number of instructions on the chip. -/
  {m : outParam Nat}
  τ : PartType
  flags : Vector ConditionalFlag m
  instrs : Vector (Instruction τ m) m

namespace Chip
variable {τ : PartType} (flags : Array ConditionalFlag) (instrs : Array (_root_.Instruction Nat τ.InternalReg τ.XBus τ.SimpleIO))

@[expose] abbrev mk'.jmpLabelsInBounds : Bool :=
  instrs.all fun
    | .jmp dst => dst < instrs.size
    | _ => true

/-- A more convenient constructor for `Chip` with default `by decide` proofs. -/
@[expose]
def mk' (flagsAndInstrs : Array (ConditionalFlag × _root_.Instruction Nat τ.InternalReg τ.XBus τ.SimpleIO))
    (h : mk'.jmpLabelsInBounds flagsAndInstrs.unzip.snd := by decide) : Chip :=
  let m := flagsAndInstrs.size
  match h' : flagsAndInstrs.unzip with
  | (flags, instrs) =>
    let instrs' : Array (Instruction τ m) :=
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
    @Chip.mk m τ ⟨flags, by simp [this]; rfl⟩ ⟨instrs', by simp [instrs', this]; rfl⟩

/-- Advance the instruction pointer to the next enabled location (possibly wrapping around or,
  rarely, getting stuck if there are no enabled locations). Does not handle `jmp` instructions. -/
def advanceIP {m} (flags : Vector ConditionalFlag m)
    : InstructionState σ m → InstructionState σ m := fun is =>
    match is.ip with
    | .none => is -- TODO I think this is right for the case where there are no instructions
    | .ofFin ip =>
      match IP.nextIP flags ip is.cond with
      | none => is -- TODO I think this is ok because if we ever lack a next IP it'll stay that way forever (?)
      | some ip' =>
        is.setIP ip' -- just set the new IP

/-- `IOEffects τ m α` wraps `α` and mutable `InstructionState m` state inside `IOEffects`.
  Equal to `InstructionState m → IOEffects XBus SimpleIO (α × InstructionState m)`. -/
@[reducible]
private def Effects (τ : PartType) (m : ℕ) : Type → Type :=
  StateT (τ.InstructionState m) (IOEffects τ.XBus τ.SimpleIO)

/-- Calculate the effect of a single instruction on some `InstructionState`, excluding effects within a single time unit (i.e. changing state between CPU cycles/ticks).
  The effects include advancing the instruction pointer. -/
def instructionEffects {m} (instr : Instruction τ m) (flags : Vector ConditionalFlag m)
    : τ.InstructionState m → IOEffects τ.XBus τ.SimpleIO (τ.InstructionState m) :=
  let res := impl *> setNextIP
  fun s => res s <&> Prod.snd
where
  /-- Here we tell ensure that `.pure` states (whether buried under other `IOEffects` or not)
    advance the instruction pointer. -/
  setNextIP : Effects τ m Unit := do
    match instr with
    | .jmp ip' => modify (InstructionState.setIP ip')
    | _ => modify (advanceIP flags)

  /-- Handle everything except for updating the IP -/
  impl : Effects τ m Unit := do
    -- TODO: somewhere (maybe here) set the conditional flag corresponding to "@" after executing this instr
    match instr with
    -- Basic
    | .nop => return
    | .mov src dst =>
      let d ← readRegOrInt src
      match dst with
      | .null => return
        -- TODO: add helper to `Effects` for this stuff
      | .internal reg => modify fun s => { s with registers := τ.inst.write reg d s.registers }
      | .simpleIO i =>
        let d := d.toSimpleIOData
        ret (.simpleIOWrite i d pure)
      | .xBus x => ret (.xBusWrite x d pure)
    | .jmp _ => return -- handled in `setNextIP`
    | .slp ri =>
      let d ← readRegOrInt ri
      match d.clampToNat with
      | 0 => return
      | k + 1 => ret <| .sleep (k + 1) (Nat.succ_ne_zero _) pure
    | .slx r => ret (.xBusPoll r pure)
    -- Arithmetic
    | .add ri => doArith ri (· + ·)
    | .sub ri => doArith ri (· - ·)
    | .mul ri => doArith ri (· * ·)
    | .not => modify (.modifyAcc (inst := τ.inst) Integer.not) -- TODO clunky
    | .dgt ri => doArith ri Integer.getDigit -- set `acc` to the `ri`th digit of `acc`
    | .dst ri₁ ri₂ =>
      -- set the `ri₁`th digit of `acc` to `ri₂`
      let digit ← readRegOrInt ri₁
      let num ← readRegOrInt ri₂
      modify (.modifyAcc (inst := τ.inst) (Integer.setDigit · digit num))
    -- Test (comparison)
    | .teq ri₁ ri₂ => doCmp ri₁ ri₂ (· == ·)
    | .tgt ri₁ ri₂ => doCmp ri₁ ri₂ (· > ·)
    | .tlt ri₁ ri₂ => doCmp ri₁ ri₂ (· < ·)
    | .tcp ri₁ ri₂ =>
      let d₁ ← readRegOrInt ri₁
      let d₂ ← readRegOrInt ri₂
      modify fun state => { state with cond := ⟨state.cond.hasRun, d₁ < d₂, d₁ > d₂⟩ }

  /-- Read an integer from `ri` (inside `Effects τ m`) -/
  readRegOrInt (ri : RegOrInt τ) : Effects τ m Integer := do
    match ri with
    | .int n => return n
    | .null => return 0
    | .internal reg => return Registers.read (self := τ.inst) reg (←get).registers -- TODO clunky
    | .xBus x => do ret (.xBusRead x pure)
    | .simpleIO i => do ret (.simpleIORead i (pure ∘ SimpleIOData.toInteger))

  /-- Set the `acc` register to `f acc (←readRegOrInt ri)`. -/
  doArith (ri : RegOrInt τ) (f : Integer → Integer → Integer) : Effects τ m Unit := do
    let d ← readRegOrInt ri
    have := τ.inst -- TODO clunky
    modify (.modifyAcc' f d)

  /-- Run the comparison function `f` with `ri₁` and `ri₂` as inputs, then
    update the conditional flags accordingly. -/
  doCmp (ri₁ ri₂ : RegOrInt τ) (f : Integer → Integer → Bool) : Effects τ m Unit := do
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify (.setCondIff (f d₁ d₂))

  /-- Return an `IOEffects` within the greater monad -/
  ret {m α} (bfx : IOEffects τ.XBus τ.SimpleIO α) : Effects τ m α :=
    fun is => bfx <&> (·, is)

/-- The state of an executing chip -/
public structure State where
  -- Constant. Not a type parameter because then we'd just have to do `(m : ℕ) × State m` inside
  -- `Vector`s below anyway
  m : ℕ

  -- Similarly to `m`, this is not a type parameter
  τ : PartType

  -- Only changes at instruction boundaries
  instructionState : IOEffects τ.XBus τ.SimpleIO (τ.InstructionState m)

  -- now, the state that can be mutated between ticks inside an instruction

  /-- The values being written out of each simple I/O pin. Reading
    from a pin sets this value to 0 (but the read value is just the max of all the other writers on this wire).
    See `resolveSimpleIO...` below.

    This may change from one CPU cycle to another within an instruction.
    For example, this occurs in the instruction `mov p0 x0` if the chip was writing something
    out of `p0` before this instruction. -/
  simpleIOOut : Vector SimpleIOData τ.numSimpleIOPins
  -- TODO do I also need to keep track of a boolean flag for each simple I/O pin here?

  /-- See the documentation comments in `MC4000.lean`. This represents whether each
    XBus pin is ready to write. This may change between CPU cycles inside an instruction because
    XBus writes set it and XBus reads clear it. -/
  waitingToWrite : Vector Bool τ.numXBusPins

instance : Inhabited State where
  default := {
    m := 1,
    τ := default,
    instructionState := pure (show InstructionState Unit 1 from default)
    simpleIOOut := #v[],
    waitingToWrite := #v[]
  }

namespace State

public def blank (τ : PartType) (m : ℕ) : State :=
  { m, τ,
    instructionState := pure
      { registers := τ.blank,
        cond := ⟨Vector.replicate _ false, false, false⟩,
        ip := IP.null },
    simpleIOOut := Vector.replicate _ 0, waitingToWrite := Vector.replicate _ false }

@[inline] def setWaitingToWrite (s : State) (i : s.τ.XBus) (val : Bool) : State :=
  { s with waitingToWrite := Vector.set s.waitingToWrite i val }

public def toString (s : State) [ToString s.τ.InternalRegState] (inputs : List Integer := []) (indent : Nat := 0) : String :=
  let ws := String.whitespace indent
  ws ++ ("\n" ++ ws).intercalate [
    s!"m = {s.m}",
    s!"simpleIOOut = {s.simpleIOOut.toList}",
    s!"waitingToWrite = {s.waitingToWrite.toList}",
    s!"instructionState = \n{s.instructionState.toString inputs (indent + 2)}"
  ]

end State
end Chip

/-- The data in the simulation that doesn't change during execution. -/
public structure Board (n : ℕ) where
  chips : Vector Chip n
  simpleIOConns : Conns n (chips[·].τ.numSimpleIOPins)
  xBusConns : Conns n (chips[·].τ.numXBusPins)

public def Board.initialStates (b : Board n) : Vector Chip.State n :=
  b.chips.map fun { m, τ, .. } => .blank τ m

namespace Chip

/-! ## XBus semantics
  I believe that when a chip executes an XBus read or write, the XBus pin sets a flag to
  indicate to all connected pins that it is waiting to read/write (or neither, but I don't think both? TODO).

  A chip with its writing flag set on some XBus pin checks for a connected pin with its reading flag set
  and, if one exists, resolves the write (clearing the flags, advancing both chip states to the next
  part of the instruction or the next instruction). Similarly for reads

  I notice there is an asymmetry between reads and writes, in that writes seem to take an extra tick to resolve.
  I don't think this is ad-hoc behavior but rather a consequence of the order of flag sets and checks. I think the
  order is `tick start` < `set own waiting-to-read flag` < `check flags` < `set own waiting-to-write flag` < `tick end`.
  This allows reads to resolve within one tick but makes writes take at least two ticks (?, TODO)

  Equivalently (I think TODO), the read flags don't need to be global variables if reads are solely
  responsible for checking flags. So the ordering becomes
    `tick start` < `each chip reading XBus resolves with a connected pin that has set its own waiting-to-write flag previously`
                 < `each chip writing XBus sets its own waiting-to-write flag`
                 < `tick end`.
-/

/-- Compute the first index of an XBus write in `states` s.t. it is on a pin connected to `whichPin`,
    its `alreadyTicked` bit is not set, and its `waiting-to-write` flag is set.
    Also return the `(outPin, d, next)` arguments to the `.xBusWrite` constructor. -/
def findWrite? (states : Vector State n) (alreadyTicked : Vector Bool n)
    (xBusConns : Conns n (states[·].τ.numXBusPins)) (whichPin : Conns.Node n (states[·].τ.numXBusPins))
    : Option ((j : Fin n) × states[j].τ.XBus × Integer × (Unit → IOEffects states[j].τ.XBus states[j].τ.SimpleIO (states[j].τ.InstructionState states[j].m))) :=
  Fin.findSome? (n := n) fun j =>
    if !alreadyTicked[j] then
      match h : states[j] with
      | ⟨m, τ, .xBusWrite pin d next, _, waitingToWrite⟩ =>
        let pin' : states[j].τ.XBus := cast (by simp [h]) pin
        if waitingToWrite[pin] && xBusConns.connected whichPin ⟨j, pin'⟩ then
          some ⟨j, pin', d, cast (by simp [h]) next⟩
        else none
      | _ => none
    else none

def resolveXBusReadOrPeek (states : Vector State n) (alreadyTicked : Vector Bool n)
    (xBusConns : Conns n (states[·].τ.numXBusPins))
    (i : Fin n) : Vector State n × Vector Bool n :=
  if alreadyTicked[i] then (states, alreadyTicked)
  else
    match states[i].instructionState with
    | .xBusRead pin next =>
      match findWrite? states alreadyTicked xBusConns ⟨i, pin⟩ with
      | .some ⟨j, pin', d, next'⟩ =>
        let states' := states
          |>.set i { states[i] with instructionState := next d }
          -- TODO: somewhere else in some comment I say that this is tolerant of multiple writes, idt that's true since we clear `waitingToWrite[pin]` here? Think about this
          |>.set j { states[j] with instructionState := next' (), waitingToWrite := states[j].waitingToWrite.set pin' false }
        (states', alreadyTicked) -- Don't update mask— we might have more "free" operations (second bullet point below) to do
      | none => (states, alreadyTicked.set i true) -- update mask since this read blocks, meaning we're done for the tick
    | .xBusPoll pin next =>
      match findWrite? states alreadyTicked xBusConns ⟨i, pin⟩ with
      | .some ⟨j, _, _, next'⟩ =>
        let states' := states
          |>.set i { states[i] with instructionState := next () }
          -- don't resolve the write since this is just a poll
        (states', alreadyTicked)
      | none => (states, alreadyTicked.set i true) -- update mask since this poll blocks
    | _ => (states, alreadyTicked)

def sameInvariants (states states': Vector State n) : Prop :=
  ∀ i : Fin n, states[i].m = states'[i].m ∧ states[i].τ = states'[i].τ

theorem sameInvariants_refl {states : Vector State n} : sameInvariants states states :=
  fun _ => ⟨rfl, rfl⟩

theorem sameInvariants_resolveXBusReadAndPeek {states : Vector State n} {alreadyTicked conns i}
    : sameInvariants states (resolveXBusReadOrPeek states alreadyTicked conns i).1 := by
  intro j
  unfold resolveXBusReadOrPeek
  refine ⟨?_, ?_⟩
  all_goals
    repeat' split <;> try rfl
    · simp only [Fin.getElem_fin, Vector.getElem_set]
      split <;> (try split) <;> simp [*]
    · simp only [Fin.getElem_fin, Vector.getElem_set]
      split <;> simp [*]

/-- Try to resolve the outermost XBus reads and peeks with writes for which the
  waiting-to-write flag has been set and `alreadyTicked` is `false`.
  `alreadyTicked[i] = true` indicates that `states[i]` has already been ticked and should be ignored.

  If there are multiple writers enabled as such, the order is unspecified (but really left-to-right in `states`). -/
def resolveXBusReadsAndPeeks {n : ℕ} (states : Vector State n)
    (xBusConns : Conns n (states[·].τ.numXBusPins))
    (alreadyTicked : Vector Bool n) : Vector State n × Vector Bool n :=
  let (⟨states', _⟩, alreadyTicked') : Subtype (sameInvariants states) × _ := (List.finRange n).foldl
    (init := (⟨states, sameInvariants_refl⟩, alreadyTicked))
    fun (⟨states, h⟩, alreadyTicked) i =>
      letI castConns := cast (by simp_all [sameInvariants]) xBusConns
      match h' : resolveXBusReadOrPeek states alreadyTicked castConns i with
      | (states', alreadyTicked') =>
        have : sameInvariants states states' := by
          have : _ = states' := congrArg Prod.fst h'
          rw [←this]; apply sameInvariants_resolveXBusReadAndPeek
        (⟨states', by grind [sameInvariants]⟩, alreadyTicked')
  (states', alreadyTicked')

/-- Each chip writing XBus sets its own `waiting-to-write` flag. -/
def setXBusWriteFlags {n : ℕ} (states : Vector State n) : Vector State n :=
  states.map fun
    | s@{ instructionState := .xBusWrite pin .., .. } => s.setWaitingToWrite (cast (by simp [*]) pin) true
    | other => other

/-- Mark everywhere we are `.sleep`ing or `.pure` as having ticked -/
def setMaskForPureAndSleep {n} (states : Vector State n) (alreadyTicked : Vector Bool n) : Vector Bool n :=
  (states.zip alreadyTicked).map fun (⟨_, _, is, _, _⟩, b) =>
    match is with
    | .sleep .. | .pure _ => true
    | _ => b

/-- Resolve all outermost`IOEffects.simpleIOWrite`s (meaning the outermost constructor of a `State.instructionState`)
  by overwriting `simpleIOOut` with the written value wherever a write occurs.
  Ignores wherever `alreadyTicked[i] = true`. -/
def resolveSimpleIOWrites {n : ℕ}
  (states : Vector State n) (alreadyTicked : Vector Bool n) : Vector State n :=
  (states.zip alreadyTicked).map fun
    | (s, true) => s
    | (s@⟨m, τ, instructionState, simpleIOOut, waitingToWrite⟩, false) =>
      match instructionState with
      | .simpleIOWrite pin d next => ⟨m, τ, next (), simpleIOOut.set pin d, waitingToWrite⟩
      | _ => s


/-- Resolve all outermost `IOEffects.simpleIORead`s by reading the max of connected chips' `simpleIOOut` fields and setting `simpleIOOut`
  to zero wherever a read occurs. Note that this uses `originalSimpleIOOuts`, i.e. those
  from the start of the tick before any simple I/O reads or writes occurred. This function
  also ignores wherever `alreadyTicked[i] = true`. -/
def resolveSimpleIOReads {n : ℕ}
    (states : Vector State n)
    (simpleIOConns : Conns n (states[·].τ.numSimpleIOPins))
    (originalSimpleIOOuts : Vector (Array SimpleIOData) n)
    (alreadyTicked : Vector Bool n) : Vector State n :=
  Vector.ofFn fun i =>
    match hs : states[i] with
    | s@⟨m, τ, instructionState, simpleIOOut, waitingToWrite⟩ =>
      if alreadyTicked[i] then s
      else
        match h' : instructionState with
        | .simpleIORead pin next =>
          let max : SimpleIOData := simpleIOConns.neighbors ⟨i, cast (by simp [hs]) pin⟩
            |>.map (fun (v : Conns.Node _ _) => originalSimpleIOOuts[v.i][v.j]!) -- TODO prove `[v.j]` is ok (will need more hypotheses)
            |>.max?
            |>.getD 0
          ⟨m, τ, next max, simpleIOOut.set pin 0, waitingToWrite⟩
        | _ => s

section

/-! Theorems to help help prove that `advanceTick` (specifically `stepUntilDone`) terminates. We eventually show below that
  `step` never increases the number of `false`s in `alreadyTicked`. -/

theorem setMaskForPureAndSleep_count_le (s t) : (setMaskForPureAndSleep s t (n := n)).count false ≤ t.count false :=
  calc
    _ ≤ (s.zip t).countP fun (_, b) => !b := Vector.countP_map_le_countP (by grind)
    _ ≤ ((s.zip t).map Prod.snd).countP fun b => !b := by rw [Vector.countP_map]; apply Vector.countP_mono_left; simp
    _ = (t.map fun b => !b).countP id := by simp [Vector.map_snd_zip]
    _ ≤ _ := by rw [Vector.count_eq_countP]; apply Vector.countP_map_le_countP; simp

-- theorem resolveXBusReadOrPeek_count_le : (resolveXBusReadOrPeek)

theorem resolveXBusReadsAndPeeks_count_le (s xc t) : (resolveXBusReadsAndPeeks s xc t (n := n)).2.count false ≤ t.count false := by
  simp only [resolveXBusReadsAndPeeks, Fin.getElem_fin]
  let motive (x : Subtype (sameInvariants s) × Vector Bool n) : Prop :=
    x.2.count false ≤ t.count false
  show motive _
  apply List.foldlRecOn
  · exact Nat.le_of_eq rfl
  · intro (s, t') (h : t'.count false ≤ t.count false) i _
    -- TODO clean up
    unfold motive resolveXBusReadOrPeek
    split
    · assumption
    · simp_all only [List.mem_finRange, Fin.getElem_fin]
      split
      · split
        · assumption
        · simp only [Vector.count_set, beq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          omega
      · simp_all only [Fin.getElem_fin, Bool.not_eq_true]
        split
        · assumption
        · simp only [Vector.count_set, beq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.sub_le_iff_le_add]; omega
      · assumption

end

/-! ## What happens in a tick
  In a tick (CPU cycle), a chip does exactly one of the following:
  - Sleeps (as in `slp`, not `slx`). At the end of the tick, the instruction pointer only advances
    to the next instruction (advancing by one tick and time unit as well) if all other chips are also sleeping.
  - Executes an initial, contiguous sequence of simple I/O, computation (like `add`), and/or *unblocked* XBus operations,
    i.e. those for which connected pins have their flags set appropriately. Due to the (equivalent) orderings above,
    this last item includes XBus reads and peeks (`slx`) for which there was a writer at the end of the previous tick.
    It also includes XBus writes for which the `waiting-to-write` flag is set *and* there is a connected reader
    at the start of the tick; note that this can never happen on the first tick an XBus write is executed.

    This sequence continues until the end of the current instruction (in which case the instruction pointer is advanced)
    or a blocked XBus operation or a sleep (as in the case of the `gen` hidden instruction). In particular,
    `teq x0 x1` would take only one tick to execute as long as `x0` and `x1` each had a writer the *previous* tick (and
    another reader did not resolve with them this tick).

    (In particular, this means that further operations after a write could continue in the same tick,
    although with the current instruction set this never happens in practice. But since `advanceTick`
    accepts arbitrarily nested `IOState` constructors, we still have to handle it.)
  - Waits on a blocked XBus operation.
-/

-- TODO how does this relate to the exec, read, sleep, write, etc. states displayed on MC4000 chips?

/-- Advance one CPU cycle across many interconnected chips.

  A simple I/O read will use the previous `simpleIOOuts`s; it does not see new data from connected chips writing
  in the same tick. (TODO confirm this)

  Increment the instruction pointer for each chip whose instruction has finished completely (i.e. ending in a `IOEffects.pure` state).
  Then use `instructionEffects` to compute (and set) the `IOEffects` of the new instruction on the pure state.

  The effect of running this function `n` times for large `n` should be to get all chips
  stuck waiting for XBus I/O to/from other chips, done with the current instruction and moved on to
  the next (i.e. `.pure`), or sleeping for a time. -/
public def advanceTick {n : ℕ} (board : Board n) (states : Vector State n) : Vector State n :=

  -- First, any pure states (meaning about to execute an instruction) get wrapped in `IOEffects`
  -- by `instructionEffects`. This is so that we can just pass in totally blank states, and I
  -- think it makes more sense this way
  let states := states.mapFinIdx' fun i s@{ m, instructionState := fx, .. } =>
    match fx with
    | .pure is =>
      match is.ip with
      | .none => s -- TODO I think this is right for the case where there are no instructions
      | .ofFin ip =>
        if h : board.chips[i].m ≠ m then
          -- TODO: prove this invariant
          panic! "The chip and the state disagree about the number of instructions on the chip"
        else
          -- TODO: also assert that the right flags are enabled for this instr.
          -- TODO: also assert other things about the current state

          let fx' := instructionEffects (board.chips[i].instrs[ip]) board.chips[i].flags (cast sorry is)
          { s with instructionState := cast sorry fx' }
    | _ => s

  -- See `stepUntilDone`
  let states := stepUntilDone states (Vector.replicate n false)
  -- TODO I think we can use `alreadyTicked` to diagnose programs that never sleep


  -- We used to advance the instruction pointer for any `.pure` states here.
  -- But `instructionEffects` does that for us now
  -- (of course, the update is only apparent in the `.pure` state, i.e. at the end of the tick)

  states

where
  originalSimpleIOOuts : Vector (Array SimpleIOData) n :=
    states.map (·.simpleIOOut.toArray)

  /-- Keep applying `step` until no further progress can be made, in which case
    we're ready to end the tick. -/
  stepUntilDone (states : Vector State n) (alreadyTicked : Vector Bool n) : Vector State n :=
    match _h: step states alreadyTicked with -- this instead of `let` for the decreasing proof
    | (states', alreadyTicked') =>
      -- TODO: this conditional is equivalent to alreadyTicked' == alreadyTicked, so prove it and simplify this expression
      if alreadyTicked'.count false == alreadyTicked.count false then states'
      else stepUntilDone states' alreadyTicked' -- run until we don't make progress
  termination_by alreadyTicked.count false
  decreasing_by
    rename_i originalStates h'
    have : alreadyTicked' = (advanceTick.step board originalStates states alreadyTicked).2 :=
      by simp_all
    subst alreadyTicked'
    apply Nat.lt_of_le_of_ne ?_ (by grind)
    calc
      _ ≤ (setMaskForPureAndSleep states alreadyTicked).count false := resolveXBusReadsAndPeeks_count_le ..
      _ ≤ _ := setMaskForPureAndSleep_count_le ..

  -- TODO: make the code match this description. I don't think we need to pass around `alreadyTicked`
  -- to the called functions. it should be much cleaner to do it in here (?)
  /-- One step within processing a tick. For every state that hasn't already been ticked, update
    it according to the outermost constructor, i.e. try to resolve simple I/O and XBus as far as possible
    until getting blocked by XBus or reaching `.sleep` or `.pure`. -/
  step (states : Vector State n) (alreadyTicked : Vector Bool n) : Vector State n × Vector Bool n :=
    -- TODO probably don't need this since the below functions don't do anything more to `.pure` and `.sleep` states
    let alreadyTicked := setMaskForPureAndSleep states alreadyTicked

    -- TODO double check that using the simpleIOOuts from the start of this tick is correct
    -- TODO something about sub-tick ordering? What about with simple I/O writes clearing their pin's buffer?
    let states := resolveSimpleIOReads states (cast sorry board.simpleIOConns) originalSimpleIOOuts alreadyTicked
    let states := resolveSimpleIOWrites states alreadyTicked

    let (states, alreadyTicked) := resolveXBusReadsAndPeeks states (cast sorry board.xBusConns) alreadyTicked
    let states := setXBusWriteFlags states

    (states, alreadyTicked)
    -- TODO does order matter here?

-- TODO somewhere enforce "cannot read pin twice"
-- TODO test edge case behavior for e.g. `mov x0 x0` or `mov p0 p0`

@[expose]
public def advanceTimeUnit.defaultMaxFuel : ℕ := 10_000

/-- Advance one time unit across many interconnected chips. This can only happen
  if every chip is in the `IOEffects.sleep` state or `IOEffects.xBusPoll` (or empty, with no instructions TODO check this).
  `.sleep` corresponds to the `slp` instruction, and `.xBusPoll` corresponds to the `.slx` instruction.

  Until all chips are empty, we call `advanceTick`.
  Sometimes chips *never* sleep, so `fuel` serves as an upper bound on the number of iterations.
  This function returns success, i.e. whether we returned before `fuel` hit zero.

  If successful, the instruction pointer of any chips that have finished sleeping (remember
  that chips can sleep for multiple time units) is incremented (or set in the case of a `.jmp`).
   -/
public def advanceTimeUnit {n : ℕ} (board : Board n)
    (states : Vector State n) (fuel : ℕ := advanceTimeUnit.defaultMaxFuel) : Bool × Vector State n :=
  match fuel with
  | 0 => (false, states)
  | k + 1 =>
    -- TODO we should also advance if some chips can't execute any instructions I think
    if h : states.all fun s => s.instructionState.isSleep then
      -- TODO is any of the tick state affected after sleeping?
      let states' := states
        |>.attachWith (fun s => s.instructionState.isSleep) (Vector.all_eq_true'.mp h)
        |>.map fun ⟨s, hs⟩ =>
          { s with instructionState := s.instructionState.advanceSleep hs }
      (true, states')
    else
      -- TODO could terminate early if no states change
      let states' := advanceTick board states
      advanceTimeUnit board states' k
