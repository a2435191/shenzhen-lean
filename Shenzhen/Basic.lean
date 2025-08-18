import Shenzhen.Integer
import Shenzhen.SimpleIOData
import Shenzhen.Instruction

namespace MC4000

@[reducible] def numXBusPins := 2
@[reducible] def XBus := Fin numXBusPins
@[reducible] def numSimpleIOPins := 2
@[reducible] def SimpleIO := Fin numSimpleIOPins
inductive InternalReg | acc -- Only one register
deriving Repr
end MC4000

inductive CondFlag | none | pos | neg | once
deriving Repr

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

end State

@[reducible]
def Instruction (numInstr : Nat) :=
  _root_.Instruction (Fin numInstr) InternalReg XBus SimpleIO

end MC4000

open MC4000 in
structure MC4000 where
  /-- The number of instructions on the chip. -/
  {m : outParam Nat}
  [inst : NeZero m]
  instrs : Vector (CondFlag × Instruction m) m
  state : State m := .init m
deriving Repr

namespace MC4000
variable (instrs : Array (CondFlag × _root_.Instruction Nat InternalReg XBus SimpleIO))

def mk'.jmpLabelsInBounds : Prop :=
  ∀ pair ∈ instrs, match pair with
    | (_, .jmp to) => to < instrs.size
    | _ => True

instance mk'.instDecidable_jmpLabelsInBounds : DecidablePred mk'.jmpLabelsInBounds :=
  fun instrs =>
    let b := instrs.all fun
      | (_, .jmp to) => to < instrs.size
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
  let instrs' : Array (CondFlag × Instruction m) :=
    instrs.attach.map fun ⟨(f, i), h⟩ => Prod.mk f <| match i with
      | .jmp to => .jmp ⟨to, hm₂ _ h⟩
      | .nop => .nop | .not => .not
      | .slp x => .slp x | .slx x => .slx x
      | .mov x y => .mov x y | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .dgt x => .dgt x
      | .dst x y => .dst x y
      | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y
  @MC4000.mk m ⟨hm₁⟩ ⟨instrs', by rw [Array.size_map, Array.size_attach]⟩ state

end MC4000

/-- `PinStateM` wraps values of type `α` in a monad that
  records pin read actions within a chip with XBus and simple IO pins.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*O pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`).
  - `ε` is the type of data read over simple IO pins (probably `SimpleIOData`). -/
inductive PinStateM (ξ : Type u) (ι : Type v) (δ : Type w) (ε : Type x) (α : Type y)
/-- Wrap a value in `PinStateM` without signaling the need for a read or write. -/
| pure : α → PinStateM ξ ι δ ε α
/-- `writeXBus pin d` represents some data `d` being written to
  XBus pin `pin`. Note that writing is a terminal action and does
  not otherwise change the state, so there is no `α` argument. -/
| writeXBus (pin : ξ) (d : δ)
/-- `writeSimpleIO pin d` represents some data `d` being written to
  simple IO pin `pin`. Note that writing is a terminal action and does
  not otherwise change the state, so there is no `α` argument. -/
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

@[reducible] def MC4000.PinStateM (m : Nat) :=
  _root_.PinStateM XBus SimpleIO (State m → Integer) (State m → SimpleIOData)

open MC4000 in
def instructionEffects {m} (instr : Instruction m) : PinStateM m (State m → State m) :=
  let readRI ri : MC4000.PinStateM m (State m → Integer) := match ri with
    | .int k => pure (fun _ => k)
    | .null => pure (fun _ => 0)
    | .internal .acc => pure State.acc
    | .simpleIO pin => .readSimpleIO pin fun d => pure (SimpleIOData.toInteger ∘ d)
    | .xBus pin => .readXBus pin pure

  let binFun ri f := do
    let d ← readRI ri
    return fun state => state.modifyAcc f (d state)

  let binRel ri₁ ri₂ r := do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state => state.setCondIff (r (fa state) (fb state))

  match instr with
  -- Basic instructions
  | .nop => pure id
  | .mov ri r => do
    let d ← readRI ri
    match r with
    | .null => return id
    | .internal .acc => return fun state => { state with acc := d state }
    | .simpleIO pin => .writeSimpleIO pin (Integer.toSimpleIOData ∘ d)
    | .xBus pin => .writeXBus pin d
  | .jmp l =>
    return ({ · with ip := l })
  | .slp ri => do
    let slpTime := Int16.toNatClampNeg ∘ Integer.n ∘ (←readRI ri)
    return fun state => { state with sleep := .slp (slpTime state)  }
  | .slx p =>
    return ({ · with sleep := .slx p })
  -- Arithmetic instructions
  | .add ri => inline (binFun ri Add.add)
  | .sub ri => inline (binFun ri Sub.sub)
  | .mul ri => inline (binFun ri Mul.mul)
  | .not =>
    return fun state => { state with acc := ~~~state.acc }
  | .dgt ri => inline (binFun ri Integer.dgt)
  | .dst ri₁ ri₂ => do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state => { state with acc := Integer.dst state.acc (fa state) (fb state) }
  -- Test instructions
  | .teq ri₁ ri₂ => inline (binRel ri₁ ri₂ BEq.beq)
  | .tgt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· > ·))
  | .tlt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· < ·))
  | .tcp ri₁ ri₂ => do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return fun state =>
      let a := fa state
      let b := fb state
      { state with cond := ⟨a > b, a < b⟩ }

structure Conns (α : Type u) where
  edges : Array (Array α)
  disjoint : ∀ i j : Fin edges.size, i ≠ j → ∀ x ∈ edges[i], x ∉ edges[j]
deriving Repr

def Conns.mk' (edges : Array (Array α)) (disjoint := by decide) :=
  Conns.mk edges disjoint

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns (Fin n × Fin MC4000.numSimpleIOPins)
  xBusConns : Conns (Fin n × Fin MC4000.numXBusPins)
deriving Repr

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
def lightController : Board :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0, 0, 100, 0, 100, 0, 100, 0]
  let touch : MC4000 :=
    let instrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 0))]
    .mk' instrs
  let chip₁ : MC4000 :=
    let instrs := #[
      (.none, .teq (.internal .acc) (.int 0)),
      (.pos,  .teq (.simpleIO 0) (.int 100)),
      (.pos,  .mov (.int 1) (.xBus 1)),
      (.neg,  .mov (.int 0) (.xBus 1)),
      (.none, .mov (.simpleIO 0) (.internal .acc)),
      (.none, .slp (.int 1))]
    { m := 6, instrs := instrs.toVector }
  let chip₂ : MC4000 :=
    let instrs := #[
      (.none, .slx 0),
      (.none, .teq (.xBus 0) (.int 1)),
      (.pos,  .add (.int 50)),
      (.none, .tgt (.internal .acc) (.int 100)),
      (.pos,  .mov (.int 0) (.internal .acc)),
      (.none, .mov (.internal .acc) (.simpleIO 1))
    ]
    { m := 6, instrs := instrs.toVector }
  let light : MC4000 :=
    { instrs := #v[
      (.none, .mov (.simpleIO 1) (.internal .acc)),
      (.none, .slp (.int 1))] }
  {
    chips := #v[touch, chip₁, chip₂, light],
    simpleIOConns := .mk' #[#[(0, 0), (1, 0)], #[(2, 1), (3, 1)]],
    xBusConns := .mk' #[#[(1, 1), (2, 0)]]
  }
