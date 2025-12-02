import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.XBusEffects

namespace MC4000

@[reducible] def numXBusPins := 2
@[reducible] def XBus := Fin numXBusPins
@[reducible] def numSimpleIOPins := 2
@[reducible] def SimpleIO := Fin numSimpleIOPins

inductive InternalReg | acc -- Only one register
deriving Repr, Lean.ToExpr

end MC4000

namespace MC4000

structure State (numInstr : Nat) where
  acc : Integer
  cond : ConditionalState
  ip : Option (Fin numInstr)
  sleep : Nat
  simpleIOOut : Vector SimpleIOData numSimpleIOPins
  /-- Whether an instruction has been executed already. Used
  to implement the `@` conditional (`ConditionalFlag.once`). -/
  hasRun : Vector Bool numInstr
deriving Repr

abbrev Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

abbrev RegOrInt :=
  _root_.Instruction.RegOrInt InternalReg XBus SimpleIO

namespace State

instance {m} : ToString (State m) where
  toString
  | { acc, cond := c, ip, sleep, simpleIOOut, hasRun } =>
    let condStr := match c with
      | ⟨true, false⟩ => "+"
      | ⟨false, true⟩ => "-"
      | ⟨false, false⟩ => "none"
      | ⟨true, true⟩ => "?both true?"
    s!"[acc = {acc}; ip = {ip}; sleep = {sleep}; \
    cond = {condStr}; simpleIOOut = ({simpleIOOut[0]}, {simpleIOOut[1]})]; \
    hasRun = {hasRun.toList.zipIdx.filter Prod.fst}"

def init (m) : State m :=
  { acc := 0,
    cond := ⟨false, false⟩,
    ip := if h : m = 0 then none else some ⟨0, Nat.zero_lt_of_ne_zero h⟩,
    sleep := 0,
    simpleIOOut := #v[0, 0],
    hasRun := Vector.replicate m false }

instance : Inhabited (State m) :=
  ⟨init m⟩

@[inline, specialize]
def modifyAcc (f : Integer → Integer) : State m → State m :=
  fun state => { state with acc := f state.acc }

/-- Set `acc` to `f acc other`. -/
@[inline, specialize]
def modifyAcc' (f : Integer → Integer → Integer) (other : Integer) : State m → State m :=
  modifyAcc (f · other)

@[inline] def setSimpleIOOut (i : SimpleIO) (val : SimpleIOData) : State m → State m
| state@{ simpleIOOut, .. } => { state with simpleIOOut := simpleIOOut.set i val }

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline] def setCondIff (b : Bool) : State m → State m :=
  fun state => { state with cond := ⟨b, !b⟩ }

/-- Set the instruction pointer to the next enabled instruction
(depending on the `+`, `-`, and `@` flags set in the source code), or `none`
 if no such instruction exists. This latter case can occur in e.g.
 chips with only `@` instructions. -/
@[specialize flags 3] def nextIp (flags : Vector ConditionalFlag m) (state : State m) : State m :=
  letI ip := do flags.nextFinIdx? (←state.ip) fun
    | _, .none => true
    | _, .pos => state.cond.posEnabled
    | _, .neg => state.cond.negEnabled
    | i, .once => !state.hasRun[i]
  { state with ip := ip }

end MC4000.State

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

def mk'.jmpLabelsInBounds : Prop :=
  ∀ pair ∈ instrs, match pair with
    | .jmp dst => dst < instrs.size
    | _ => True

instance mk'.instDecidablePred : DecidablePred mk'.jmpLabelsInBounds :=
  fun instrs =>
    let b := instrs.all fun
      | .jmp dst => dst < instrs.size
      | _ => true
    decidable_of_bool b <| by
      simp only [b, jmpLabelsInBounds, Array.all_iff_forall, Nat.zero_le, true_and, forall_self_imp]
      rw [←Array.forall_getElem]
      constructor
      all_goals
        intro h i ih
        have := h i ih
        split <;> simp_all

/-- A more convenient constructor for `MC4000` with default `by decide` proofs. -/
def mk' (flagsAndInstrs : Array (ConditionalFlag × _root_.Instruction Nat InternalReg XBus SimpleIO))
    (h : mk'.jmpLabelsInBounds flagsAndInstrs.unzip.snd := by decide) : MC4000 :=
  let m := flagsAndInstrs.size
  match h' : flagsAndInstrs.unzip with
  | (flags, instrs) =>
    let instrs' : Array (Instruction m) :=
      instrs.attach.map fun ⟨i, hi⟩ =>
        match i with
        | .jmp dst => .jmp ⟨dst, by
            have := h (.jmp dst) (h' ▸ hi)
            rwa [Array.snd_unzip, Array.size_map] at this⟩
        | .nop => .nop | .not => .not
        | .slp x => .slp x | .slx x => .slx x
        | .mov x y => .mov x y | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .dgt x => .dgt x
        | .dst x y => .dst x y
        | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y
    have : flags = flagsAndInstrs.unzip.1 ∧ instrs = flagsAndInstrs.unzip.2 := ⟨h' ▸ rfl, h' ▸ rfl⟩
    @MC4000.mk m ⟨flags, by simp [this]; rfl⟩ ⟨instrs', by simp [instrs', this]; rfl⟩

end mk'

namespace State

/-! Instruction effects -/
abbrev InstructionEffects := XBusEffects XBus Integer
abbrev InstructionEffects.Read? := XBusEffects.Read? XBus Integer

variable {m : ℕ} (simpleIOIn : Vector SimpleIOData numSimpleIOPins) (state : State m)

/-- Read a register or integer literal, considering only the XBus effects.
    Simple I/O effects are handled in `handleSimpleIO`. -/
@[inline]
def next.readXBus₁ : RegOrInt → InstructionEffects.Read? Integer
| .xBus x => .read₁ x id
| .simpleIO x => .none simpleIOIn[x]
| .internal .acc => .none state.acc
| .null => .none 0
| .int literal => .none literal

def next.readXBus₂ (ri₁ ri₂ : RegOrInt) : InstructionEffects.Read? (Integer × Integer) :=
  have : _ ∧ _ := by
    constructor
    all_goals
      unfold XBusEffects.Read?.isRead₂ next.readXBus₁
      (repeat split at *)
      <;> trivial
  .seq (r₁ := next.readXBus₁ simpleIOIn state ri₁) (r₂ := next.readXBus₁ simpleIOIn state ri₂) this.1 this.2

/-- Get the state after executing the current instruction, possibly wrapped in XBus pin reads/a poll/a write.
  Will try to advance the state regardless of `state.sleep` or `state.hasRun`.
 -/
@[specialize flags instrs]
def execCurrentInstr (flags : Vector ConditionalFlag m) (instrs : Vector (Instruction m) m) : InstructionEffects (State m) :=
  match state.ip with
  | none => pure state
  | some ip =>
    letI state' := state.nextIp flags
    match instrs[ip] with
    | .nop => pure state'
    | .mov src dst =>
      let val := next.readXBus₁ simpleIOIn state src
      -- TODO : move at least this call into a monad (?)
      let state' := handleSimpleIO src state'
      match dst with
      | .xBus y => .write y (val <&> (·, state'))
      | .simpleIO y => .ofRead? <| val <&> fun d =>
          state'.setSimpleIOOut y d.toSimpleIOData
      | .internal .acc => .ofRead? <| val <&> ({ state' with acc := · })
      | .null => .ofRead? (val <&> fun _ => state')
    | .jmp l => pure { state with ip := some l }
    | .slp src =>
      let state' := handleSimpleIO src state'
      ofRead₁ src ({ state' with sleep := ·.clampToNat })
    | .slx xBusReg =>
      -- src is `XBus` so no need to handle simple I/O
      -- TODO: check the game's behavior
      -- to make sure that after `slx` we go
      -- straight to the next instruction.
      -- Otherwise stay on the original `state`
      .poll xBusReg state'
    | .add src =>
      let state' := handleSimpleIO src state'
      ofRead₁ src (state'.modifyAcc' Integer.add)
    | .sub src =>
      let state' := handleSimpleIO src state'
      ofRead₁ src (state'.modifyAcc' Integer.sub)
    | .mul src =>
      let state' := handleSimpleIO src state'
      ofRead₁ src (state'.modifyAcc' Integer.mul)
    | .not => pure (state'.modifyAcc Integer.not)
    | .dgt src =>
      let state' := handleSimpleIO src state'
      ofRead₁ src (state'.modifyAcc' Integer.getDigit)
    | .dst src₁ src₂ =>
      let state' := handleSimpleIO₂ src₁ src₂ state'
      ofRead₂ src₁ src₂ fun digit new => state'.modifyAcc (Integer.setDigit · digit new)
    | .teq src₁ src₂ =>
      let state' := handleSimpleIO₂ src₁ src₂ state'
      ofRead₂ src₁ src₂ fun x y => state'.setCondIff (x == y)
    | .tgt src₁ src₂ =>
      let state' := handleSimpleIO₂ src₁ src₂ state'
      ofRead₂ src₁ src₂ fun x y => state'.setCondIff (x > y)
    | .tlt src₁ src₂ =>
      let state' := handleSimpleIO₂ src₁ src₂ state'
      ofRead₂ src₁ src₂ fun x y => state'.setCondIff (x < y)
    | .tcp src₁ src₂ =>
      let state' := handleSimpleIO₂ src₁ src₂ state'
      ofRead₂ src₁ src₂ fun x y => { state' with cond := ⟨x > y, x < y⟩ }
where
  /-- Reading in from simple I/O clears any previously set simple output (to 0). -/
  handleSimpleIO : RegOrInt → State m → State m
    | .xBus _ | .internal _ | .null | .int _ => id
    | .simpleIO x => State.setSimpleIOOut x 0

  handleSimpleIO₂ : RegOrInt → RegOrInt → State m → State m :=
    fun ri₁ ri₂ state => state |> handleSimpleIO ri₁ |> handleSimpleIO ri₂

  ofRead₁ (ri : RegOrInt) (f : Integer → State m) : InstructionEffects (State m) :=
    let val := next.readXBus₁ simpleIOIn state ri
    .ofRead? (f <$> val)

  ofRead₂ (ri₁ ri₂ : RegOrInt) (f : Integer → Integer → State m) : InstructionEffects (State m) :=
    let val := next.readXBus₂ simpleIOIn state ri₁ ri₂
    .ofRead? (Function.uncurry f <$> val)



-- namespace InstructionEffects

-- variable {m} (initState : State m) (prevSimpleIOIn : PrevSimpleIOIn)

-- @[inline] def run (fx : InstructionEffects m α) : XBusEffects XBus Integer (α × State m) :=
--   fx prevSimpleIOIn initState

-- @[inline] def run' (fx : InstructionEffects m Unit) : XBusEffects XBus Integer (State m) :=
--   Prod.snd <$> fx prevSimpleIOIn initState
