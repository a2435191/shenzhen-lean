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

@[reducible]
def Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

namespace State

def init (m) [NeZero m] : State m :=
  { acc := 0,
    cond := ⟨false, false⟩,
    ip := 0,
    sleep := 0,
    simpleIOOut := #v[0, 0] }

instance [NeZero m] : Inhabited (State m) :=
  ⟨init m⟩

@[inline]
def modifyAcc (state : State m) (f : Integer → Integer → Integer) (other : Integer) :=
  { state with acc := f state.acc other }

/-- Enable `pos` and disable `neg` instructions if `b` holds.
  Otherwise, disable `pos` and enable `neg` instructions. -/
@[inline]
def setCondIff  (b : Bool) (state : State m) :=
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
variable (instrs : Array (ConditionalFlag × _root_.Instruction Nat InternalReg XBus SimpleIO))

def mk'.jmpLabelsInBounds : Prop :=
  ∀ pair ∈ instrs, match pair with
    | (_, .jmp «to») => «to» < instrs.size
    | _ => True

instance mk'.instDecidable_jmpLabelsInBounds : DecidablePred mk'.jmpLabelsInBounds :=
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
