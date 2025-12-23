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

def connections (conns : Conns χ ψ) (chip : χ) (pin : ψ) : List (χ × ψ) :=
  conns.edges.find? (List.contains · (chip, pin))
    |>.getD []
    |>.filter (· != (chip, pin))

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

def Board.State.ofXBusEffects {m} : XBusEffects MC4000.XBus Integer (MC4000.State m) → Board.State :=
  mk m

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
    MC4000.mk' flagsAndInstrs (by simp [flagsAndInstrs])
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

namespace Board

@[inline] private def _root_.Vector.set₂ {n} (xs : Vector α n) (i : Fin n) (x : α) (j : Fin n) (y : α) :=
  xs.set i x|>.set j y

/-- Advance chip states one tick, communicating between chip pins:
  - If a chip's state `s` is stuck waiting on an XBus read (write) on pin `p`,
    resolve it with the first chip stuck waiting on an XBus write (read)
    on a pin connected to `p`. (i.e. move both states one step out of `XBusEffects`.)
    If no such other chip exists, don't change `s`.
  - If the chip state `s` is sleeping on an XBus pin `x` (via the `slx` instruction), we
    look for the first chip stuck waiting to write out of a pin connected to `x` and advance only
    `s`, since `slx` doesn't actually read in the value from the other chip.
  - For simple I/O, the values are not wrapped in something like `XBusEffects`. Instead,
    each pin takes in (i.e. this is `simpleIOIn` in `MC4000.next`) the maximum of all the
    output values of pins connected to it, not including itself.
    These are computed from the `simpleIOOut` arrays for each chip.
-/
def next (board : Board) (states : Vector State board.n) : Vector State board.n :=
  List.finRange board.n
    |>.foldl go (states, Vector.replicate board.n false)
    |>.fst
where go :=
  let originalStates := states
  fun (states, used) i =>
    if used[i] then (states, used) -- skip
    else
      let ⟨m, fx⟩ := states[i]
      let xBusConns := board.xBusConns.connections i
      match fx with
      | .poll pin afterWake =>
        -- The original states because another chip's write can still wake us
        -- even if it's read by something else the same tick
        let canWake := originalStates.zipFinIdx.any fun (⟨_, fx'⟩, j) =>
          !used[j] && match fx' with
            | .write pin' (.pure _) =>
              board.xBusConns.areConnected (i, pin) (j, pin')
            | _ => false
        if canWake then (states, used)
        else (states.set i ⟨m, pure afterWake⟩, used.set i true)
      | .ofRead? (.read₁ pin ofData) => sorry
      | .ofRead? (.read₂ pin₁ pin₂ ofData) => sorry
      | .write pin (.pure (d, afterWrite)) =>
        let reader? : Option (State × Fin board.n) := originalStates.zipFinIdx.findSome? fun (⟨m', fx'⟩, j) =>
          if used[j] then none else match fx' with
            | .ofRead? (.read₁ pin' ofData) =>
              if board.xBusConns.areConnected (i, pin) (j, pin') then
                some (State.mk m' (pure <| ofData d), j)
              else none
            | .ofRead? (.read₂ pin'₁ pin'₂ ofData) =>
              if board.xBusConns.areConnected (i, pin) (j, pin'₁) then
                some (State.mk m' (.ofRead? <| .read₁ pin'₂ (ofData d)), j)
              else none
            | _ => none
        match reader? with
        | none => (states, used)
        | some (otherStateAfterRead, j) =>
          (states.set₂ i ⟨m, pure afterWrite⟩ j otherStateAfterRead,
           used.set i true)
      | .write pin _ => sorry
      | .pure s => /- TODO: handle simple I/O here -/ sorry
