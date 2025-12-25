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

/-- The instruction pointer for an `MC4000` with `m` instructions. -/
abbrev IP (m) := Option (Fin m)

structure State (numInstr : Nat) where
  acc : Integer
  cond : ConditionalState numInstr
  ip : IP numInstr
  sleep : Nat
deriving Repr

abbrev Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

abbrev RegOrInt :=
  _root_.Instruction.RegOrInt InternalReg XBus SimpleIO

namespace State

instance {m} : ToString (State m) where
  toString
  | { acc, cond := c, ip, sleep } =>
    let condStr := match c.boolFlags with
      | (true, false) => "+"
      | (false, true) => "-"
      | (false, false) => "none"
      | (true, true) => "?both true?"
    s!"[acc = {acc}; ip = {ip}; sleep = {sleep}; \
    cond = {condStr}; \
    hasRun = {c.hasRun.toList.zipIdx.filter Prod.fst}"

def init (m) : State m :=
  { acc := 0,
    cond := ⟨Vector.replicate m false, false, false⟩,
    ip := if h : m = 0 then none else some ⟨0, Nat.zero_lt_of_ne_zero h⟩,
    sleep := 0 }

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
            unfold m
            simp only [mk'.jmpLabelsInBounds, Array.all_eq_true', ←h'] at h
            replace h := h (.jmp dst) hi
            rw [decide_eq_true_eq] at h
            convert h
            simp [h']
        | .nop => .nop | .not => .not
        | .slp x => .slp x | .slx x => .slx x
        | .mov x y => .mov x y | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .dgt x => .dgt x
        | .dst x y => .dst x y
        | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y
    have : flags = flagsAndInstrs.unzip.1 ∧ instrs = flagsAndInstrs.unzip.2 := ⟨h' ▸ rfl, h' ▸ rfl⟩
    @MC4000.mk m ⟨flags, by simp [this]; rfl⟩ ⟨instrs', by simp [instrs', this]; rfl⟩

end mk'

namespace State

abbrev SimpleIOIn := Vector SimpleIOData numSimpleIOPins

/-! Instruction effects -/
abbrev InstructionEffects α :=
  StateM SimpleIOIn <| XBusEffects XBus Integer α

abbrev ReadEffects := XBusEffects.Read? XBus Integer

variable {m : ℕ}

section
variable (simpleIOIn : Vector SimpleIOData numSimpleIOPins) (state : State m)

/-- Read a register or integer literal, considering only the XBus effects.
    Simple I/O effects are handled in `handleSimpleIO`. -/
@[inline] def execCurrentInstr.read₁ : RegOrInt → ReadEffects Integer
| .xBus x => .read₁ x id
| .simpleIO x => .none simpleIOIn[x]
| .internal .acc => .none state.acc
| .null => .none 0
| .int literal => .none literal

@[inline] def execCurrentInstr.read₂ (state : State m) (ri₁ ri₂ : RegOrInt) : ReadEffects (Integer × Integer) :=
  have : _ ∧ _ := by
    constructor
    all_goals
      unfold XBusEffects.Read?.isRead₂ read₁
      (repeat split at *)
      <;> trivial
  .seq (read₁ simpleIOIn state ri₁) (read₁ simpleIOIn state ri₂)
       this.1 this.2
end

/-! ## A note about simple I/O
  "At any given time, a simple I/O pin is either in input mode or output mode. Writing a value
  to a pin register will put the corresponding pin into output mode with the specified output value.
  Reading a value from a pin register will put the corresponding pin into input mode, clearing any
  previously set output value." (copied from the manual)

  This is the only effect that can change the state of a chip mid-instruction. -/

/-- Get the state after executing the current instruction, possibly wrapped in XBus pin reads/a poll/a write.
  - If the current instruction pointer is `none`, we try to go to the first available instruction (see `nextIP`).
  - Otherwise, we execute `instrs[state.ip]` regardless of the flags/internal conditional registers or `state.sleep`. The next
  state returned also ignores the `+`/`-`/`@` registers. It's just `state.advanceIP` unless the instruction is `jmp l`,
  in which case it jumps to `l`.
 -/
@[specialize instrs]
private def execCurrentInstr
    (instrs : Vector (Instruction m) m) (state : State m) : InstructionEffects (State m) :=
    show StateM _ _ from do
  match state.ip with
  | none => return pure (state.modifyIP IP.succ)
  | some ip =>
    let instr := instrs[ip]
    let simpleIOIn ← get
    -- TODO
    -- State.setHasRun ip true <$>
    -- State.modifyIP (IP.next instr) <$>
    handleSimpleIO instr; -- TODO: check the corner case when `mov` reads from and writes to the same I/O register
    match instr with
    | .nop => return pure state
    | .mov src dst =>
      let read? := execCurrentInstr.read₁ simpleIOIn state src
      match dst with
      | .xBus y => return .write y (read? <&> (·, state))
      | .simpleIO y => return .ofRead? <| read? <&> fun d =>
          sorry
      | .internal .acc => return .ofRead? <| read? <&> ({ state with acc := · })
      | .null => return .ofRead? (read? <&> fun _ => state)
    | .jmp _ => return pure state -- handled by `IP.next` above
    | _ => sorry
    -- | .slp src =>
    --   ofRead?₁ src ({ state with sleep := ·.clampToNat })
    -- | .slx xBusReg => .poll xBusReg state
    -- | .add src =>
    --   ofRead?₁ src (state.modifyAcc' Integer.add)
    -- | .sub src =>
    --   ofRead?₁ src (state.modifyAcc' Integer.sub)
    -- | .mul src =>
    --   ofRead?₁ src (state.modifyAcc' Integer.mul)
    -- | .not => pure (state.modifyAcc Integer.not)
    -- | .dgt src =>
    --   ofRead?₁ src (state.modifyAcc' Integer.getDigit)
    -- | .dst src₁ src₂ =>
    --   ofRead?₂ src₁ src₂ fun digit new =>
    --     state.modifyAcc (Integer.setDigit · digit new)
    -- | .teq src₁ src₂ =>
    --   ofRead?₂ src₁ src₂ fun x y => state.setCondIff (x == y)
    -- | .tgt src₁ src₂ =>
    --   ofRead?₂ src₁ src₂ fun x y => state.setCondIff (x > y)
    -- | .tlt src₁ src₂ =>
    --   ofRead?₂ src₁ src₂ fun x y => state.setCondIff (x < y)
    -- | .tcp src₁ src₂ =>
    --   ofRead?₂ src₁ src₂ fun x y => { state with cond := ⟨state.cond.hasRun, x > y, x < y⟩ }
where
  /-- Reading in from simple I/O clears any previously set simple output (to 0). -/
  clearSimpleOutput : RegOrInt → StateM SimpleIOIn Unit
    | .xBus _ | .internal _ | .null | .int _ => pure ()
    | .simpleIO x => modify (Vector.set · x 0)

  handleSimpleIO : Instruction m → StateM SimpleIOIn Unit
    -- in slx, the src register is XBus, so no need to handle simple I/O
    | .nop | .not | .slx _ | .jmp _ => pure ()
    | .mov s _ | .slp s | .add s | .sub s | .mul s | .dgt s =>
      clearSimpleOutput s
    | .dst s t | .teq s t | .tgt s t | .tlt s t | .tcp s t =>
      clearSimpleOutput s *> clearSimpleOutput t

  -- /-- Read a single value and write nothing. Simple I/O effects are not handled here, only XBus. -/
  -- @[inline] ofRead?₁ (ri : RegOrInt) (f : Integer → State m) : InstructionEffects (State m) :=
  --   let val := execCurrentInstr.read₁ simpleIOIn state ri
  --   .ofRead? (f <$> val)

  -- @[inline] ofRead?₂ (ri₁ ri₂ : RegOrInt) (f : Integer → Integer → State m) : InstructionEffects (State m) :=
  --   let val := execCurrentInstr.read₂ simpleIOIn state ri₁ ri₂
  --   .ofRead? (Function.uncurry f <$> val)

/-- Get the state after executing the current instruction, possibly wrapped in XBus pin reads/a poll/a write.
  - If `state.sleep = 0`, this executes `instrs[state.ip]` regardless of the flags/internal conditional registers.
  - However, in this case the state returned after executing the current instruction will
    have its IP at the next enabled point (see `nextIP`). The conditional registers used are updated according to the instruction,
    so `teq 0 0; teq 0 1; + nop; slp 1` jumps over the `nop` to the `slp` instruction. This is also the case
    for `jmp` instructions, for which the IP is the first after the destination or the destination itself.
  - Additionally, `state.sleep > 0` will return `state` instead of executing anything. Note that this does not
    decrement the sleep counter. That only happens at the end of a time unit (see Application Note 393 in the manual).
  - If the current instruction pointer is `none`, we try to go to the first available instruction
    (see `nextIP`).
 -/
@[specialize flags instrs]
def next
    (flags : Vector ConditionalFlag m) (instrs : Vector (Instruction m) m)
    (state : State m) (simpleIOIn : Vector SimpleIOData numSimpleIOPins)
    : InstructionEffects (State m) :=
  if state.sleep == 0 then
    execCurrentInstr instrs state simpleIOIn <&> fun state' =>
      -- the IP is now just the successor of the original `state.ip` (or the jmp target)
      -- now advance the IP to the nearest enabled value (including the current one)
      state'.modifyIP (IP.currOrNextEnabled flags state'.cond)
  else pure state
