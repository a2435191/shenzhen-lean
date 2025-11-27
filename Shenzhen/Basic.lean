-- import Shenzhen.Board
import Shenzhen.Compile
-- import Shenzhen.Examples
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.XBusEffects
structure Conns (χ : Type u) (ψ : Type v) where
  edges : Array (List (χ × ψ)) -- each edge is `(chip, pin)`
  nontrivial : ∀ edge ∈ edges, edge.length ≥ 2 := by decide
  nodupChips : ∀ edge ∈ edges, List.Nodup (edge.unzip.fst) := by decide
  disjoint : ∀ i j : Fin edges.size, i ≠ j → ∀ x ∈ edges[i], x ∉ edges[j] := by decide
deriving Repr

namespace Conns

instance : Inhabited (Conns χ ψ) :=
  ⟨#[], nofun, nofun, nofun⟩

variable [DecidableEq χ] [DecidableEq ψ]

-- TODO: cache this result ahead of time in `Board` in a `Std.HashMap` or something
/-- Get the index of the neighbors to `(chip, pin)`, including `(chip, pin)` itself. -/
def edgeIdx (conns : Conns χ ψ) (chip : χ) (pin : ψ) : Option (Fin (conns.edges.size)) :=
  conns.edges.findFinIdx? ((chip, pin) ∈ ·)

-- TODO: compute this result ahead of time
def areConnected (conns : Conns χ ψ) : χ × ψ → χ × ψ → Bool
| u, v => conns.edges.any fun edge => u ∈ edge && v ∈ edge

end Conns

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns (Fin n) MC4000.SimpleIO
  xBusConns : Conns (Fin n) MC4000.XBus
deriving Repr

structure Board.State where
  m : Nat
  xBusEffects : XBusEffects MC4000.XBus Integer (MC4000.State m)

structure Board.States (b : Board) where
  states : Vector Board.State b.n
  hm : ∀ i : Fin b.n, states[i].m = b.chips[i].m
  simpleIOByEdge : Vector SimpleIOData b.simpleIOConns.edges.size

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch :=
    let flagsAndInstrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 1))]
    MC4000.mk' flagsAndInstrs
  let chip₁ := MC4000.ofCompiled mcc(
      teq acc 0
    + teq p0 100
    + mov 1 x1
    - mov 0 x1
      mov p0 acc
      slp 1)
  let chip₂ := MC4000.ofCompiled mcc(
      slx x0
      teq x0 p1
    + add 50
      tgt acc 100
    + mov 0 acc
      mov acc p1)
  let light := MC4000.ofCompiled mcc(
    mov p1 acc
    slp 1)
  {
    chips := #v[touch, chip₁, chip₂, light],
    simpleIOConns := { edges := #[[(0, 0), (1, 0)], [(2, 1), (3, 1)]] },
    xBusConns := { edges := #[[(1, 1), (2, 0)]] }
  }

-- open MC4000 MC4000.State in
-- #eval Id.run do
--   let n := 4
--   let m := 6
--   let lc := lightController
--   let states : Vector ((m : Nat) × State m) n := #v[
--     ⟨8, .init 8⟩,
--     ⟨6, .init 6⟩,
--     ⟨6, .init 6⟩,
--     ⟨2, .init 2⟩]
--   let simpleIOs : Array SimpleIOData := lc.simpleIOConns.edges.map fun edge =>
--     edge.map (fun (chip, pin) => states[chip]!.snd.simpleIOOut[pin])
--       |> @List.max? _ maxOfLe
--       |>.getD 0
--   for h : i in [0:n] do
--     let ⟨m, state⟩ := states[i]
--     let (flag, instr) := lc.chips[i].instrs[state.ip]!
--     let x :=
--       if state.flagEnabled flag then
--         some (instructionEffects instr)
--       else none
--     break
--   -- let fx := Vector.ofFn (n := n) (fun i =>
--   --   let ⟨m, state⟩ := states[i]
--   --   let (flag, instr) := lc.chips[i].instrs[state.ip]!
--   --   if state.flagEnabled flag then
--   --     some <| Sigma.mk i $ (instructionEffects instr)
--   --   else
--   --     none)

@[inline, specialize]
private def writer? (areNeighbors : Fin n × ξ → Fin n × ξ → Bool) (i : Fin n) (readPin : ξ) (candidates : Vector (Bool × XBusEffects ξ δ α) n) : Option (Fin n × ξ × δ × α) :=
  candidates.zipIdx.attach.firstM fun ⟨((didStep, fx), j), h⟩ =>
    letI j := Fin.mk j (Vector.mem_zipIdx' h).left
    match didStep, fx with
    | false, .write writePin d a =>
      if areNeighbors (i, readPin) (j, writePin) then
        some (j, writePin, d, a)
      else none
    | _, _ => none

@[specialize]
def resolveXBus (areNeighbors : Fin n × ξ → Fin n × ξ → Bool) (fx : Vector (XBusEffects ξ δ α) n)
    : Vector (Bool × XBusEffects ξ δ α) n :=
  (List.finRange n).foldl (init := ((Vector.replicate n false).zip fx)) fun v i =>
    match v[i] with
    | (true, _) | (false, .pure _) | (false, .write ..) => v
    | (false, .read pin next) =>
      match writer? areNeighbors i pin v with
      | none => v
      | some (j, _, d, a) => v.set i (true, next d) |>.set j (true, pure a)
    | (false, .peek pin a) =>
      match writer? areNeighbors i pin v with
      | none => v
      | some _ => v.set i (true, pure a)

/-- Step a board's states one cycle, which is the time it takes to complete a single `nop` instruction. -/
def step (board : Board) (states : board.States) : Array (Fin board.n × MC4000.XBus) × board.States :=
  let allXBusEffects := Vector.ofFn (n := board.n) fun i =>
    let prevSimpleIO := Vector.ofFn fun j =>
      let edgeIdx := board.simpleIOConns.edgeIdx i j
      (states.simpleIOByEdge.get <$> edgeIdx).getD 0
    let { m, xBusEffects } := states.states[i]
    Sigma.mk m <$> xBusEffects
  let resolved := resolveXBus board.xBusConns.areConnected allXBusEffects
  let hangs := ((Vector.ofFn id).zip resolved).toArray.filterMap fun
    | (i, false, .read pin _)
    | (i, false, .write pin ..) => some (i, pin)
    | _ => none
  (hangs, sorry)

#check Sigma

#print MC4000.State
