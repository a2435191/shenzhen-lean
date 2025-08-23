import Shenzhen.MCParser

@[specialize] private def next (arr : Vector α n) (p : α → Bool) (i : Fin n)
    (h : ∃ a ∈ arr, p a) : Fin n :=
  List.finRange n
    |>.map (· + i)
    |>.filter (p arr[·])
    |>.get ⟨0, by
      simp only [Vector.mem_iff_getElem] at h
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
def nextInstructionLine {lines : Vector (MCParser.Line Λ ρ ξ ι) n}
    (i : Fin n) (h : ∃ line ∈ lines, line.instruction.isSome) : Fin n :=
  next lines (·.instruction.isSome) i h

variable (lines : Vector (MCParser.Line Λ ρ ξ ι) n)
  [BEq Λ] [Hashable Λ]

inductive CompileException (n : Nat)
| noInstructions
| duplicateLabels (i : Fin n)
| unknownLabelInJmp (i : Fin n)
deriving Inhabited

/-- Create a mapping from `Λ` labels to positions in the array.
If a label is on a line with an instruction, it gets sent to the next
instruction via `nextInstructionLine`. -/
def labelPositions : Except (CompileException n) (Std.HashMap Λ (Fin n)) :=
  if h : ∃ line ∈ lines, line.instruction.isSome then
    lines.mapFinIdx (fun i a hi => (Fin.mk i hi, a))
      |>.foldlM (b := {}) fun map (i, line) =>
        match line.label with
        | none => .ok map
        | some s =>
          if _ : map.contains s then
            .error (.duplicateLabels i)
          else
            let next := nextInstructionLine i h
            .ok (map.insert s next)
  else .error .noInstructions

-- def replaceJmpLabels [BEq Λ] [Hashable Λ] (labelsMap : Std.HashMap Λ (Fin n)) : Except (CompileException n) (Vector (MCParser.Line (Fin n) ρ ξ ι) n) := do
--   lines.mapFinIdxM fun i { label, condition, instruction, comment } hi => do
--     let label' ← label.mapM fun l =>
--       match labelsMap[l]? with
--       | none => panic! s!"`labelsMap` is missing the label at line {i} of `lines`"
--       | some j => .ok j
--     let instruction' ← instruction.mapM <| Instruction.mapΛM fun l =>
--       match labelsMap[l]? with
--       | none => .error (.unknownLabelInJmp ⟨i, hi⟩)
--       | some j => .ok j
--     .ok ⟨label', condition, instruction', comment⟩

-- @[always_inline] private def Fin.pred' : Fin n → Fin n
-- | ⟨0, _⟩ => ⟨n - 1, by grind⟩
-- | ⟨k + 1, _⟩ => ⟨k, by grind⟩


/-- Compile a vector of `MCParser.Line`s to a vector of `ConditionalFlag × Instruction`s.
All lines without instructions are discarded. -/
def compile : Except (CompileException n) ((m : Nat) × Vector (ConditionalFlag × Instruction (Fin m) ρ ξ ι) m) := do
  let labelMap ← labelPositions lines

  let noBlanks := lines.zip (Vector.ofFn id)|>.toArray.filterMap fun
    | ({ instruction := none, .. }, _) => none
    | ({ instruction := some instr, condition, .. }, i) => some (i, condition, instr)

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

  return ⟨noBlanks.size, instrs⟩

-- structure compile.State (Λ : Type u) [BEq Λ] [Hashable Λ] (ρ : Type v) (ξ : Type w) (ι : Type x)
--     (n : Nat) (fuel : Fin (n + 1)) where
--   m : Fin (n - fuel + 1)
--   labelsMap : Std.HashMap Λ (Fin m)
--   instrs : Array (ConditionalFlag × Instruction (Fin m) ρ ξ ι)
--   h : instrs.size = m -- not a `Vector` because casting is annoying in `go`

-- def compile.State.go (fuel : Fin (n + 1)) (state : compile.State Λ ρ ξ ι n fuel) : Except (CompileException n) (compile.State Λ ρ ξ ι n 0) :=
--   match hfuel : fuel with
--   | ⟨0, _⟩ => .ok state
--   | ⟨k + 1, hk⟩ => do
--     let i : Fin n := ⟨n - fuel, Nat.sub_lt_self (hfuel ▸ Nat.zero_lt_succ k) (Fin.is_le fuel)⟩
--     let line := lines[i]
--     let fuel' : Fin (n + 1) := ⟨k, Nat.lt_of_succ_lt hk⟩
--     -- let skippedCast := skipped.map (Fin.castLE (Nat.sub_le_sub_left (Nat.le_succ k) n))
--     have : n - (k + 1) + 1 ≤ n - fuel' + 1 := by
--       simp [fuel']

--       sorry
--     -- let labelsMap' ← (match line.label with
--     --     | none => return state.labelsMap.map fun _ => Fin.castLE (by simp [m'])
--     --     | some l =>
--     --       if state.labelsMap.contains l then
--     --         .error (.duplicateLabels i)
--     --       else
--     --         sorry)

--     match line.instruction with
--     | none => go fuel' { state with m := Fin.castLE this state.m }
--     | some instr =>
--       let m' := Fin.mk (state.m + 1) <| by
--         simp [fuel']
--         have := state.m.isLt
--         sorry

--       go fuel' ⟨m', sorry, sorry, sorry⟩
