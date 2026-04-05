import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.XBusEffects
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

/-- Represents the state during some tick. While executing an instruction (possibly across multiple ticks, in the case that we block on XBus),
  all fields stay the same except for `simpleIOOut`, which may change from one tick to another inside an instruction. See its notes -/
structure State (numInstr : Nat) where
  acc : Integer
  cond : ConditionalState numInstr
  ip : IP numInstr
  /-- The values being written out of each simple I/O pin. Reading
    from a pin sets this value to 0 (but the read value is just the max of all the other writers on this wire).
    See `effects`.

    This may change from one tick to another within an instruction.
    For example, this occurs in the instruction `mov p0 x0` if the chip was writing something
    out of `p0` before this instruction.
    TODO: make this an effect?  -/
  simpleIOOut : Vector SimpleIOData numSimpleIOPins
deriving Repr

abbrev Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

abbrev RegOrInt :=
  _root_.Instruction.RegOrInt InternalReg XBus SimpleIO

namespace State

instance {m} : ToString (State m) where
  toString
  | { acc, cond := c, ip, simpleIOOut } =>
    let condStr := match c.boolFlags with
      | (true, false) => "+"
      | (false, true) => "-"
      | (false, false) => "none"
      | (true, true) => "?both true?"
    s!"[acc = {acc}; ip = {ip}; \
    cond = {condStr}; \
    hasRun = {c.hasRun.toList.zipIdx.filter Prod.fst}; \
    simpleIOOut = {simpleIOOut.toList}"

def init (m) : State m :=
  { acc := 0,
    cond := ⟨Vector.replicate m false, false, false⟩,
    ip := if h : m = 0 then none else some ⟨0, Nat.zero_lt_of_ne_zero h⟩,
    simpleIOOut := Vector.replicate numSimpleIOPins 0 }

instance : Inhabited (State m) :=
  ⟨init m⟩

@[inline, specialize]
def modifyAcc (f : Integer → Integer) : State m → State m :=
  fun state => { state with acc := f state.acc }

/-- Set `acc` to `f acc other`. -/
@[inline, specialize]
def modifyAcc' (f : Integer → Integer → Integer) (other : Integer) : State m → State m :=
  modifyAcc (f · other)

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline] def setCondIff (b : Bool) : State m → State m :=
  fun state => { state with cond := ⟨state.cond.hasRun, b, !b⟩ }

@[inline] def setHasRun (which : Fin m) (b : Bool) : State m → State m :=
  fun state => { state with cond := {
    state.cond with hasRun := state.cond.hasRun.set which b }
  }

@[inline] def setIP (new : IP m) : State m → State m :=
  ({ · with ip := new })

@[inline] def modifyIP (f : IP m → IP m) : State m → State m :=
  fun state => { state with ip := f state.ip }


@[inline] def setSimpleIOOut (i : SimpleIO) (val : SimpleIOData) : State m → State m :=
  fun state => { state with simpleIOOut := Vector.set state.simpleIOOut i val }

@[inline] def clearSimpleIOOut (i : SimpleIO) : State m → State m :=
  setSimpleIOOut i 0

end State

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

/-! ## A note about simple I/O
  "At any given time, a simple I/O pin is either in input mode or output mode. Writing a value
  to a pin register will put the corresponding pin into output mode with the specified output value.
  Reading a value from a pin register will put the corresponding pin into input mode, clearing any
  previously set output value." (copied from the manual)

  This is the only effect that can change the state of a chip mid-instruction. -/

def ret {α} {m} [Functor m] : m α → ReaderT ρ (StateT σ m) α :=
  fun a _ s => (·, s) <$> a

/-- The `ReaderT` contains `simpleIOIn`, i.e. the max of the simple I/O signals over the wire for each simple I/O pin (not counting the current chip's output).
  Does not update the instruction pointer. -/
def effects {m} (instr : Instruction m) : ReaderT (Vector SimpleIOData numSimpleIOPins) (StateT (State m) (IOEffects XBus Integer)) Unit := do
  match instr with
  -- Basic
  | .nop => return
  | .mov src dst =>
    let d ← readRegOrInt src
    match dst with
    | .null => return
    | .internal .acc => modify ({· with acc := d})
    | .simpleIO i =>
      modify (setSimpleIOOut i d.toSimpleIOData)
      return
    | .xBus x =>
      ret <| .write x d pure
  | .jmp _ => return -- the jump is taken care of elsewhere
  | .slp ri =>
    let d ← readRegOrInt ri
    match d.clampToNat with
    | 0 => return
    | k + 1 => ret <| .sleep (k + 1) (by simp) pure
  | .slx r =>
    ret (.poll r pure)
  -- Arithmetic
  | .add ri => doArith ri (· + ·)
  | .sub ri => doArith ri (· - ·)
  | .mul ri => doArith ri (· * ·)
  | .not => modify (modifyAcc Integer.not)
  | .dgt ri => doArith ri Integer.getDigit -- set `acc` to the `ri`th digit of `acc`
  | .dst ri₁ ri₂ =>
    -- set the `ri₁`th digit of `acc` to `ri₂`
    let digit ← readRegOrInt ri₁
    let num ← readRegOrInt ri₂
    modify (modifyAcc (Integer.setDigit · digit num))
  -- Test (comparison)
  | .teq ri₁ ri₂ => doCmp ri₁ ri₂ (· == ·)
  | .tgt ri₁ ri₂ => doCmp ri₁ ri₂ (· > ·)
  | .tlt ri₁ ri₂ => doCmp ri₁ ri₂ (· < ·)
  | .tcp ri₁ ri₂ =>
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify fun state => { state with cond := ⟨state.cond.hasRun, d₁ < d₂, d₁ > d₂⟩ }
where
  readRegOrInt ri := do
    match ri with
    | .int i => return i
    | .null => return 0
    | .internal .acc => return (←get).acc
    | .simpleIO i => do
      modify (clearSimpleIOOut i)
      let simpleIOIn ← read
      return simpleIOIn[i]
    | .xBus x =>
      ret <| .read x pure

  doArith ri f := do
    let d ← readRegOrInt ri
    modify (modifyAcc' f d)

  doCmp ri₁ ri₂ f := do
    let d₁ ← readRegOrInt ri₁
    let d₂ ← readRegOrInt ri₂
    modify (setCondIff (f d₁ d₂))
