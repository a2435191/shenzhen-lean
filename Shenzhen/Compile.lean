import Shenzhen.MCParser

namespace Shenzhen.Compile

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
| noInstructions
| duplicateLabels (i : Fin lines.size)
| unknownLabelInJmp (i : Fin lines.size)
deriving Inhabited, Repr

/-- Create a mapping from `Λ` labels to positions in the array.
If a label is on a line with an instruction, it gets sent to the next
instruction via `nextInstructionLine`. -/
def labelPositions : Except (CompileException lines) (Std.HashMap Λ (Fin lines.size)) :=
  if h : ∃ line ∈ lines, line.instruction.isSome then
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
  else .error .noInstructions

structure Compiled (ρ : Type u) (ξ : Type v) (ι : Type w) where
  m : Nat
  instrs : Vector (ConditionalFlag × Instruction (Fin m) ρ ξ ι) m
deriving Repr

/-- Compile a vector of `MCParser.Line`s to a vector of `ConditionalFlag × Instruction`s.
All lines without instructions are discarded. -/
def compile : Except (CompileException lines) (Compiled ρ ξ ι) := do
  let labelMap ← labelPositions lines
  let n := lines.size

  let noBlanks := lines.zip (Array.ofFn (n := n) id)|>.filterMap fun
    | ({ instruction := none, .. }, _) => none
    | ({ instruction := some instr, condition, .. }, i) => some (i, condition, instr)
  let m := noBlanks.size

  let instrs ← noBlanks.toVector.mapM fun (i, cond, instr) => do
    let instr' ← instr.mapΛM fun l => do
      let targetIdx : Fin n ← match labelMap[l]? with
        | none => .error (.unknownLabelInJmp i)
        | some j => .ok j
      match noBlanks.findFinIdx? (·.1 = targetIdx) with
      | none =>
        -- since we already ran `labelPositions`, there must be some instruction
        unreachable!
      | some k => .ok k
    return (cond, instr')

  return ⟨m, instrs⟩

-- #eval
--   match compile mc(
--   slp x0
--   slx x0
-- ) with
--   | .ok compiled => println! repr compiled
--   | .error e => println! repr e
