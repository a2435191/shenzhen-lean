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
  edges : List (List (χ × ψ)) -- each edge is `(chip, pin)`
  nontrivial : ∀ edge ∈ edges, edge.length ≥ 2 := by decide
  nodupChips : ∀ edge ∈ edges, List.Nodup (edge.unzip.fst) := by decide
  disjoint : ∀ x, Subsingleton { i : Fin edges.length // x ∈ edges[i] } := by decide
deriving Repr

namespace Conns

instance : Inhabited (Conns χ ψ) :=
  ⟨[], nofun, nofun, fun _ => ⟨nofun⟩⟩

instance [DecidableEq α] {l₁ l₂ : List α} : Decidable (l₁.Disjoint l₂) :=
  decidable_of_iff (∀ x ∈ l₁, ¬x ∈ l₂) Iff.rfl

theorem _root_.forall_mem_comm' [Membership α γ] {S : γ} {p : α → β → Prop} : (∀ a ∈ S, ∀ b, p a b) ↔ ∀ b, ∀ a ∈ S, p a b := by
  constructor <;> intros <;> simp_all

instance [DecidableEq α] {l : List (List α)} : Decidable (∀ (x : α), Subsingleton { i : Fin l.length // x ∈ l[i] }) :=
  let n := l.length
  -- TODO: this is inefficient
  letI := (List.finRange n).product (List.finRange n)
    |>.all fun (i, j) => i = j || l[i].Disjoint l[j]
  decidable_of_bool this <| by
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, Prod.forall,
      List.pair_mem_product, List.mem_finRange, and_self, forall_const, subsingleton_iff,
      Subtype.forall, Subtype.mk.injEq, this, n]
    rw [forall_comm (α := α)]
    simp only [forall_mem_comm' (β := Fin l.length)]
    apply forall_congr'; intro i
    apply forall_congr'; intro j
    simp_rw [imp_iff_not_or, or_comm, ←or_assoc, or_comm, or_assoc, forall_or_left]
    apply or_congr_right
    apply forall_congr'; intro x
    tauto

-- TODO: cache this result ahead of time in `Board` in a `Std.HashMap` or something
/-- Get the neighbors to `(chip, pin)`, including `(chip, pin)` itself. -/
def toNeighbors [DecidableEq χ] [DecidableEq ψ] (conns : Conns χ ψ) (chip : χ) (pin : ψ) : List (χ × ψ) :=
  match h : conns.edges.filter ((chip, pin) ∈ ·) with
  | [] => []
  | [edge] => edge
  | x :: y :: rest => by
    exfalso
    simp only [List.filter_eq_cons_iff, decide_eq_true_eq] at h
    have ⟨l₁, l₂, h₁, h₂, h₃, l₂₁, l₂₂, h₄, h₅, h₆, h₇⟩ := h
    rw [h₄] at h₁
    apply absurd ((conns.disjoint (chip, pin)).allEq ?_ ?_) ?_
    set_option linter.unnecessarySimpa false in
    · refine ⟨⟨l₁.length, ?_⟩, ?_⟩
      <;> simpa [h₁]
    · refine ⟨⟨l₁.length + l₂₁.length + 1, ?_⟩, ?_⟩
      <;> simpa [h₁, Nat.add_assoc, Nat.add_lt_add_iff_left]
    · intro hn
      repeat injection hn with hn
      rw [Nat.add_assoc, Nat.left_eq_add] at hn
      contradiction

end Conns

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns (Fin n) MC4000.SimpleIO
  xBusConns : Conns (Fin n) MC4000.XBus
deriving Repr

structure Board.States (b : Board) where
  chipStates : Vector ((m : Nat) × MC4000.State.InstructionEffects m Unit) b.n
  h : ∀ i : Fin b.n, chipStates[i].1 = b.chips[i].m
  simpleIOByEdge : Vector SimpleIOData b.simpleIOConns.edges.length

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch :=
    let instrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 1))]
    MC4000.mk' instrs
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
    simpleIOConns := { edges := [[(0, 0), (1, 0)], [(2, 1), (3, 1)]] },
    xBusConns := { edges := [[(1, 1), (2, 0)]] }
  }

open MC4000 MC4000.State in
#eval
  let m := 3
  --                           mov p0 x1
  let instr : Instruction 3 := .mov (.simpleIO 0) (.xBus 1)
  let mfx := instructionEffects instr
  --              values on connected simple I/O line: p0  p1
  let fx := mfx |> InstructionEffects.run' (.init m) #v[35, 69]
  return fx

/-- Step a board's states one cycle, which is the time it takes to complete a single `nop` instruction. -/
def step (board : Board) (states : board.States) : board.States :=
  let chipStates := states.chipStates
  sorry
