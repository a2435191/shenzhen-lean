import Shenzhen.Line
import Shenzhen.Util

namespace Compile

@[specialize] private def next (arr : Array α) (p : α → Bool) (i : Fin arr.size)
    (h : ∃ a ∈ arr, p a) : Fin arr.size :=
  List.finRange arr.size
    |>.map (· + i)
    |>.filter (p arr[·])
    |>.get ⟨0, by
      simp only [Array.mem_iff_getElem] at h
      have ⟨a, ⟨j, hj₁, hj₂⟩, ha⟩ := h
      simp
      exists ⟨j, hj₁⟩ - i
      convert hj₂.symm ▸ ha
      simp [Fin.sub_def, Fin.add_def,
        ←Nat.sub_add_comm (Nat.le_of_lt i.isLt),
        Nat.sub_add_cancel (Nat.le_add_right_of_le (Nat.le_of_lt i.isLt))]
      exact Nat.mod_eq_of_lt hj₁⟩

/-- Get the nearest (forward) index of a line that contains an instruction,
including the current one. This could require wrapping around. -/
def nextInstructionLine {lines : Array (MCParser.Line Λ ρ ξ ι)}
    (i : Fin lines.size) (h : ∃ line ∈ lines, line.instruction.isSome) : Fin lines.size :=
  next lines (·.instruction.isSome) i h

variable (lines : Array (MCParser.Line Λ ρ ξ ι)) [BEq Λ] [Hashable Λ]

inductive CompileException
| duplicateLabels (i : Fin lines.size)
| unknownLabelInJmp (i : Fin lines.size)
deriving Repr

instance : ToString (CompileException arr) where
  toString
  | .duplicateLabels i => s!"There's a duplicate label at line {i}"
  | .unknownLabelInJmp i => s!"There's an unknown label in the `jmp` instruction at line {i}"


/-- Create a mapping from `Λ` labels to positions in the array.
If a label is on a line with an instruction, it gets sent to the next
instruction via `nextInstructionLine`. -/
def labelPositions (h : ∃ line ∈ lines, line.instruction.isSome) : Except (CompileException lines) (Std.HashMap Λ (Fin lines.size)) :=
  lines.mapFinIdx (fun i a hi => (Fin.mk i hi, a))
    |>.foldlM (init := {}) fun map (i, line) =>
      match line.label with
      | none => .ok map
      | some s =>
        if _ : map.contains s then
          .error (.duplicateLabels i)
        else
          let next := nextInstructionLine i h
          .ok (map.insert s next)

structure Compiled (ρ : Type u) (ξ : Type v) (ι : Type w) where
  m : Nat
  instrs : Vector (ConditionalFlag × Instruction (Fin m) ρ ξ ι) m
deriving Repr, Inhabited

namespace Compiled

private instance instZeroNat : Zero Nat :=
  inferInstance

private instance instDecidableNeNat {a b : Nat} : Decidable (a ≠ b) :=
  inferInstance

open Lean

variable {ρ : Type u} {ξ : Type v} {ι : Type w}
         [ToLevel.{u}] [ToLevel.{v}] [ToLevel.{w}]
         [ToExpr ρ] [ToExpr ξ] [ToExpr ι]
variable {m : Nat}

private instance instToExprProd : ToExpr (ConditionalFlag × Instruction (Fin m) ρ ξ ι) :=
  @instToExprProdOfToLevel ConditionalFlag (Instruction (Fin m) ρ ξ ι)
    _ ({ toLevel := Level.mkNaryMax [toLevel.{u}, toLevel.{v}, toLevel.{w}] }) _ _

instance : ToExpr (Compiled ρ ξ ι) :=
  let levels := [toLevel.{u}, toLevel.{v}, toLevel.{w}]
  let typeParams := #[toTypeExpr ρ, toTypeExpr ξ, toTypeExpr ι]
  { toTypeExpr := mkAppN (mkConst ``Compiled levels) typeParams,
    toExpr
    | { m, instrs, .. } =>
      let mExpr := mkNatLit m
      let instrsType := (instToExprProd (ρ := ρ) (ξ := ξ) (ι := ι) (m := m)).toTypeExpr
      let instrsExpr := Meta.mkVector instrsType (instrs.toList.map toExpr) m (.mkNaryMax levels)
      mkAppN (mkConst ``Compiled.mk levels) (typeParams ++ #[mExpr, instrsExpr])
  }

-- elab "test" : term =>
--   let : Compiled MC4000.InternalReg MC4000.XBus MC4000.SimpleIO :=
--     { m := 3, instrs := #v[(.none, .nop), (.none, .nop), (.none, .nop)] }
--   return toExpr this

-- #synth Lean.ToExpr (ConditionalFlag × ConditionalFlag)

-- #eval test

def empty : Compiled ρ ξ ι :=
  { m := 0, instrs := #v[] }

end Compiled

/-- Compile a vector of `MCParser.Line`s to a vector of `ConditionalFlag × Instruction`s.
All lines without instructions are discarded. -/
def compile : Except (CompileException lines) (Compiled ρ ξ ι) :=
  let n := lines.size

  let noBlanks := lines.zip (Array.ofFn (n := n) id)|>.filterMap fun
    | ({ instruction := none, .. }, _) => none
    | ({ instruction := some instr, condition, .. }, i) => some (i, condition, instr)

  let m := noBlanks.size
  if h : m = 0 then return .empty
  else
    have h := Nat.zero_lt_of_ne_zero h
    have := by
      have ⟨(line, i), hmem, (i', flag, instr), h⟩ := Array.size_filterMap_pos_iff.mp h
      refine ⟨line, (Array.of_mem_zip hmem).left, ?_⟩
      split at h
      · contradiction
      · rename_i h'
        rw [Prod.mk.injEq] at h'
        rw [h'.left]
        rfl
    do
    let labelMap ← labelPositions lines this

    let instrs ← noBlanks.toVector.mapM fun (i, cond, instr) => do
      let instr' ← instr.mapΛM fun l => do
        let targetIdx : Fin n ← match labelMap[l]? with
          | none => .error (.unknownLabelInJmp i)
          | some j => .ok j
        match noBlanks.findFinIdx? (·.1 = targetIdx) with
        | none =>
          -- since we already ran `labelPositions`, there must be some instruction
          have : Inhabited (Fin noBlanks.size) := ⟨0, h⟩
          unreachable!
        | some k => .ok k
      return (cond, instr')

    return Compiled.mk m instrs

end Compile

def MC4000.ofCompiled : Compile.Compiled InternalReg XBus SimpleIO → MC4000
| { m, instrs } => { m, instrs }
