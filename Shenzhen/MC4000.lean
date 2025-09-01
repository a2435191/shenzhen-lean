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
  ip : Fin numInstr
  sleep : Nat
  simpleIOOut : Vector SimpleIOData numSimpleIOPins
deriving Repr

abbrev Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

abbrev RegOrInt :=
  _root_.Instruction.RegOrInt InternalReg XBus SimpleIO

namespace State

instance {m} : ToString (State m) where
  toString
  | { acc, cond := c, ip, sleep, simpleIOOut } =>
    let condStr := match c with
      | ⟨true, false⟩ => "+"
      | ⟨false, true⟩ => "-"
      | ⟨false, false⟩ => "none"
      | ⟨true, true⟩ => "?both true?"
    s!"[acc = {acc}; ip = {ip}; sleep = {sleep}; \
    cond = {condStr}; simpleIOOut = ({simpleIOOut[0]}, {simpleIOOut[1]})]"

def init (m) [NeZero m] : State m :=
  { acc := 0,
    cond := ⟨false, false⟩,
    ip := 0,
    sleep := 0,
    simpleIOOut := #v[0, 0] }

instance [NeZero m] : Inhabited (State m) :=
  ⟨init m⟩

/-- Set `acc` to `f acc other`. -/
@[inline, specialize]
def modifyAcc (f : Integer → Integer → Integer) (other : Integer) (state : State m) :=
  { state with acc := f state.acc other }

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline]
def setCondIff (b : Bool) (state : State m) :=
  { state with cond := ⟨b, !b⟩ }

@[inline]
def incIp (state : State m) : State m :=
  { state with ip := state.ip.succ' }

end MC4000.State

open MC4000 in
structure MC4000 where
  /-- The number of instructions on the chip. -/
  {m : outParam Nat}
  [inst : NeZero m]
  instrs : Vector (ConditionalFlag × Instruction m) m
  state : State m := .init m
deriving Repr

namespace MC4000

section mk'
variable (instrs : Array (ConditionalFlag × _root_.Instruction Nat InternalReg XBus SimpleIO))

def mk'.jmpLabelsInBounds : Prop :=
  ∀ pair ∈ instrs, match pair with
    | (_, .jmp «to») => «to» < instrs.size
    | _ => True

instance mk'.instDecidablePred : DecidablePred mk'.jmpLabelsInBounds :=
  fun instrs =>
    let b := instrs.all fun
      | (_, .jmp «to») => «to» < instrs.size
      | _ => true
    decidable_of_bool b <| by
      simp only [b, jmpLabelsInBounds, Array.all_iff_forall, Nat.zero_le, true_and, forall_self_imp]
      rw [←Array.forall_getElem]
      constructor
      all_goals
        intro h i ih
        have := h i ih
        split <;> simp_all

/-- A more convenient constructor for `MC4000` with default `by decide`
    proofs. -/
def mk'
    (hm₁ : instrs.size ≠ 0 := by decide) (hm₂ : mk'.jmpLabelsInBounds instrs := by decide)
    (state : State instrs.size := @State.init _ ⟨hm₁⟩) :=
  let m := instrs.size
  let instrs' : Array (ConditionalFlag × Instruction m) :=
    instrs.attach.map fun ⟨(f, i), h⟩ => Prod.mk f <| match i with
      | .jmp «to» => .jmp ⟨«to», hm₂ _ h⟩
      | .nop => .nop | .not => .not
      | .slp x => .slp x | .slx x => .slx x
      | .mov x y => .mov x y | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .dgt x => .dgt x
      | .dst x y => .dst x y
      | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y
  @MC4000.mk m ⟨hm₁⟩ ⟨instrs', by rw [Array.size_map, Array.size_attach]⟩ state

end mk'

/-! Instruction effects -/

abbrev PrevSimpleIOIn :=
  Vector SimpleIOData numSimpleIOPins

abbrev InstructionEffects (m : Nat) :=
  ReaderT PrevSimpleIOIn $ StateT (State m) $ XBusEffects XBus Integer

@[inline] def InstructionEffects.run {m} (initState : State m)
    (prevSimpleIOIn : PrevSimpleIOIn) (fx : InstructionEffects m α) : XBusEffects XBus Integer (α × State m) :=
  fx prevSimpleIOIn initState

@[inline] def InstructionEffects.run' {m} (initState : State m)
    (prevSimpleIOIn : PrevSimpleIOIn) (fx : InstructionEffects m Unit) : XBusEffects XBus Integer (State m) :=
  Prod.snd <$> fx prevSimpleIOIn initState

/-- Get a function to the next state after executing `instr`, possibly with
XBus pin reads/a peek/a write. -/
def instructionEffects {m} (instr : Instruction m) : InstructionEffects m Unit := do
  -- increment the IP separately
  match instr with | .jmp _ => return; | _ => modify State.incIp;
  match instr with
  | .nop => return
  | .slp ri => do
    let n ← readRI ri
    modify ({ · with sleep := n.clampToNat })
  | .slx pin =>
    fun _ state => .peek pin <| return ((), state)
  | .jmp lbl => modify ({ · with ip := lbl })
  | .mov ri r => do
    let n ← readRI ri
    match r with
    | .null => return
    | .internal .acc => modify ({· with acc := n })
    | .simpleIO pin => setSimpleIOOut pin n.toSimpleIOData
    | .xBus pin => fun _ state => .write pin n ((), state)
  | .add ri => modifyAcc ri Add.add
  | .sub ri => modifyAcc ri Sub.sub
  | .mul ri => modifyAcc ri Mul.mul
  | .not => modify fun state => { state with acc := ~~~state.acc }
  | .dgt ri => modifyAcc ri Integer.dgt
  | .dst ri₁ ri₂ => do
    let target ← readRI ri₁
    let new ← readRI ri₂
    modify fun state => { state with acc := Integer.dst state.acc target new }
  | .teq ri₁ ri₂ => modifyCond ri₁ ri₂ (· = ·)
  | .tlt ri₁ ri₂ => modifyCond ri₁ ri₂ (· < ·)
  | .tgt ri₁ ri₂ => modifyCond ri₁ ri₂ (· > ·)
  | .tcp ri₁ ri₂ => do
    let a ← readRI ri₁
    let b ← readRI ri₂
    modify ({ · with cond := ⟨a > b, a < b⟩ })
where
  @[inline] setSimpleIOOut (pin : SimpleIO) (val : SimpleIOData) :=
    modify fun state => { state with simpleIOOut := Vector.set state.simpleIOOut pin val }

  @[inline] readRI : RegOrInt → InstructionEffects m Integer
    | .int n => return n
    | .null => return 0
    | .internal .acc => do return (←get).acc
    | .simpleIO pin => do
      setSimpleIOOut pin 0
      let prevSimpleIO ← read
      return prevSimpleIO[pin]
    | .xBus pin => fun _ state =>
      .read pin fun d => return (d, state)

  @[specialize, inline] modifyAcc ri f := do
    modify (State.modifyAcc f (←readRI ri))

  @[specialize, inline] modifyCond ri₁ ri₂ (f : Integer → Integer → Bool) := do
    let a ← readRI ri₁
    let b ← readRI ri₂
    modify (State.setCondIff (f a b))
