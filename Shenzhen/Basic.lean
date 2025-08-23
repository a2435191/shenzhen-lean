import Shenzhen.Compile
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.PinStateM
import Shenzhen.SimpleIOData
import Shenzhen.Util

open MC4000 in
/-- Get a function to the next state after executing `instr`, possibly with
pin reads/a pin write.
here. -/
def instructionEffects {m} (instr : Instruction m) (state : State m) : PinStateM (State m) :=
  let readRI ri := match ri with
    | .int k => pure k
    | .null => pure 0
    | .internal .acc => pure state.acc
    | .simpleIO pin => .readSimpleIO pin (pure ∘ SimpleIOData.toInteger)
    | .xBus pin => .readXBus pin pure

  let binFun ri f := do
    return state.modifyAcc f (←readRI ri)

  let binRel ri₁ ri₂ r := do
    return state.setCondIff (r (←readRI ri₁) (←readRI ri₂))

  State.nextInstr instr <$> match instr with
  -- Basic instructions
  | .nop => return state
  | .mov ri r => do
    let d ← readRI ri
    match r with
    | .null => return state
    | .internal .acc => return { state with acc := d }
    | .simpleIO pin => .writeSimpleIO pin (Integer.toSimpleIOData d) (pure state)
    | .xBus pin => .writeXBus pin d (pure state)
  | .jmp _ => return state -- just `state` since we map it through `State.nextInstr` above
  | .slp ri => do
    let slpTime := Int16.toNatClampNeg (Integer.n (←readRI ri))
    return { state with sleep := .slp slpTime }
  | .slx p => return { state with sleep := .slx p }
  -- Arithmetic instructions
  | .add ri => inline (binFun ri Add.add)
  | .sub ri => inline (binFun ri Sub.sub)
  | .mul ri => inline (binFun ri Mul.mul)
  | .not =>
    return { state with acc := ~~~state.acc }
  | .dgt ri => inline (binFun ri Integer.dgt)
  | .dst ri₁ ri₂ => do
    let fa ← readRI ri₁
    let fb ← readRI ri₂
    return { state with acc := Integer.dst state.acc fa fb }
  -- Test instructions
  | .teq ri₁ ri₂ => inline (binRel ri₁ ri₂ BEq.beq)
  | .tgt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· > ·))
  | .tlt ri₁ ri₂ => inline (binRel ri₁ ri₂ (· < ·))
  | .tcp ri₁ ri₂ => do
    let a ← readRI ri₁
    let b ← readRI ri₂
    return { state with cond := ⟨a > b, a < b⟩ }

abbrev Conns (numChips numPins : Nat) :=
  Vector (Vector (Array (Fin numChips × Fin numPins)) numPins) numChips

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns n MC4000.numSimpleIOPins
  xBusConns : Conns n MC4000.numXBusPins
deriving Repr

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch : MC4000 :=
    let instrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 1))]
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
    simpleIOConns := #v[#v[#[(1, 0)], #[]], #v[#[(0, 0)], #[]], #v[#[], #[(3, 1)]], #v[#[], #[(2, 1)]]],
    xBusConns := #v[#v[#[], #[]], #v[#[], #[(2, 0)]], #v[#[(1, 1)], #[]], #v[#[], #[]]]
  }

/-- Resolve the XBus read or write at `states[i]` given `states` (one for each chip). Returns
the result of reading/writing from `states[i]` given the context `iNeighbors`.
If that operation blocks, returns `none`. Otherwise, returns the new `states[i]`
after reading/writing, the state corresponding to the complementary XBus pin after writing/reading,
and the indices of both. Specifically, `(reader, readerIdx, writer, writerIdx)`. -/
@[inline] private def resolveXBus [BEq ξ] (states : Vector (PinStateM ξ ι δ ε α) n)
    (i : Fin n) (iNeighbors : Array (Fin n × ξ)) (h : states[i].isXBus)
    : Option (PinStateM ξ ι δ ε α × Fin n × PinStateM ξ ι δ ε α × Fin n) :=
  match h' : states[i] with
  | .readSimpleIO .. | .writeSimpleIO .. | .pure _ => by exfalso; simp_all
  | .readXBus dstPin next =>
    let writer? := iNeighbors.firstM fun (j, pin) =>
      match states[j] with
      | .writeXBus srcPin d srcNext =>
        if pin == srcPin then some (j, d, srcNext) else none
      | _ => none
    writer? <&> fun (j, d, srcNext) => (next d, i, srcNext, j)
  | .writeXBus srcPin d next =>
    let reader? := iNeighbors.firstM fun (j, pin) =>
      match states[j] with
      | .readXBus dstPin dstNext =>
        if pin == dstPin then some (j, dstNext) else none
      | _ => none
    reader? <&> fun (j, dstNext) => (dstNext d, j, next, i)

/-- Resolve the simple I/O read(s) or write(s) at `state`. If `state` is not `.writeSimpleIO ..` or `.readSimpleIO ..`, just
returns `state`. The `neighborOutValues` are any values written by neighboring I/O pins
**after the end of the previous timestep**. This ensures that all the I/O pins are updated at once within
a timestep. `onWrite` and `onRead` are how the state should be transformed after a write and read,
respectively. If `state` is composed of multiple simple I/O operations without any XBus operations in between, they will all be resolved. -/
@[inline] def resolveSimpleIO {α : Type u} [Max ε] [Zero ε] [Fintype δ] [Fintype ε]
    (state : PinStateM ξ ι δ ε α) (onWrite : ι → ε → α → α) (onRead : ι → α → α)
    (neighborOutValues : ι → Array ε) : { p : PinStateM ξ ι δ ε α // p.isSimpleIO = false } :=
  go state
where
  -- We need to reference the two `Fintype` instances
  -- to get the termination/decreasing proof to compile
  @[inline] go [Fintype δ] [Fintype ε] state :=
    match h : state with
    | .readXBus .. | .writeXBus .. | .pure _ => ⟨state, h ▸ rfl⟩
    | .writeSimpleIO srcPin d next =>
      go (onWrite srcPin d <$> next)
    | .readSimpleIO dstPin next =>
      let maxNeighbor := (neighborOutValues dstPin).foldl max 0
      go (onRead dstPin <$> next maxNeighbor)
termination_by state
decreasing_by (
  · simp [sizeOf, PinStateM.sizeOf'_map, PinStateM.sizeOf']
  · show sizeOf (onRead dstPin <$> next maxNeighbor) < sizeOf (PinStateM.readSimpleIO dstPin next)
    simp only [sizeOf, PinStateM.sizeOf'_map, PinStateM.sizeOf', Nat.lt_one_add_iff]
    apply Finset.le_max'
    rw [Finset.mem_insert]
    right
    apply Finset.mem_image_of_mem
    apply Fintype.complete)

@[specialize] def resolve {ξ ι δ ε α} [Max ε] [Zero ε] [Fintype δ] [Fintype ε] [BEq ξ]
    (states : Vector (PinStateM ξ ι δ ε α) n)
    (xBusNeighbors : Fin n → ξ → Array (Fin n × ξ)) (simpleIONeighborsOutValues : Fin n → ι → Array ε)
    (onSimpleIOWrite : ι → ε → α → α) (onSimpleIORead : ι → α → α)
    : Vector ({ p : PinStateM ξ ι δ ε α // p.isSimpleIO = false } × Bool) n :=
  -- 1. Resolve all of the available simple I/O requests.
  let resolveSimpleIO' state i :=
    resolveSimpleIO state onSimpleIOWrite onSimpleIORead (simpleIONeighborsOutValues i)
  let initResults := states.mapFinIdx fun i state ih => resolveSimpleIO' state ⟨i, ih⟩

  -- `didSteps` is "didStep" plural, not "did steps"
  let (states, didSteps) := (List.finRange n).foldl (init := (initResults, Vector.replicate n false)) fun (states, didSteps) i =>
    if didSteps[i] then (states, didSteps)
    else
      match h : states[i] with
      | ⟨.readSimpleIO .., _⟩ | ⟨.writeSimpleIO .., _⟩ => by exfalso; contradiction
      | ⟨.pure a, _⟩ => (states, didSteps)
      | ⟨.readXBus pin _, _⟩ | ⟨.writeXBus pin .., _⟩ =>
        let exchange? := resolveXBus states.unattach i (xBusNeighbors i pin) (by simp_all)
        match exchange? with
        | none => (states, didSteps)
        | some (reader, readerIdx, writer, writerIdx) => (
          states |>.set readerIdx (resolveSimpleIO' reader readerIdx) |>.set writerIdx (resolveSimpleIO' writer writerIdx),
          didSteps |>.set readerIdx true |>.set writerIdx true)
  Vector.zip states didSteps

instance : LE SimpleIOData := ⟨fun ⟨n, _⟩ ⟨m, _⟩ => n ≤ m⟩
instance : DecidableLE SimpleIOData :=
  fun ⟨n, _⟩ ⟨m, _⟩ => decidable_of_bool (n ≤ m) (by simp [LE.le])
instance : Max SimpleIOData := maxOfLe
instance : Zero SimpleIOData := ⟨0⟩
instance : Zero Integer := ⟨0⟩
instance : ToString ((m : Nat) × MC4000.State m) where
  toString | ⟨_, x⟩ => toString (repr x)

open MC4000 in
#eval
  let lc := lightController
  let effects : Vector (PinStateM ((m : Nat) × State m)) lc.n := lc.chips.map
    fun { m, instrs, state, inst } =>
      let fx := instructionEffects instrs[state.ip].snd state
      (⟨m, ·⟩) <$> fx
  let this := resolve effects
    (fun i j => lc.xBusConns[i][j])
    (fun i j => lc.simpleIOConns[i][j].map fun (i', j') => lc.chips[i'].state.simpleIOOut[j'])
    (fun pin d ⟨m, state⟩ => ⟨m, { state with simpleIOOut := state.simpleIOOut.set pin d }⟩)
    (fun pin ⟨m, state⟩ => ⟨m, { state with simpleIOOut := state.simpleIOOut.set pin 0 }⟩)
  for (x, b) in this do
    println! toString x
