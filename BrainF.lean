inductive Instruction (addr : Type u)
| right               -- >
| left                -- <
| incr                -- +
| decr                -- -
| out                 -- .
| in                  -- ,
| fwd (target : addr) -- [
| bwd (target : addr) -- ]
deriving DecidableEq

def Instruction.parse? : Char → Option (Instruction Unit)
| '>' => some right
| '<' => some left
| '+' => some incr
| '-' => some decr
| '.' => some out
| ',' => some .in
| '[' => some (fwd ())
| ']' => some (bwd ())
| _ => none

structure Program where
  size : Nat
  instrs : Vector (Instruction (Fin size)) size

namespace Program

def empty : Program where
  size := 0
  instrs := #v[]

-- inductive ParseError (charsSize : Nat)
-- | noMatchingFwd (loc : Fin charsSize)
-- | noMatchingBwd (loc : Fin charsSize)


@[inline] def _root_.Fin.succ' : Fin n → Fin n
| ⟨i, h⟩ => ⟨(i + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt h)⟩

def computeInstructionAddr (instrs : Array (Instruction Unit)) (stack : List (Fin instrs.size))
    (i : Fin instrs.size)
    : Except String (List (Fin instrs.size) × Instruction (Fin instrs.size)) :=
  match instrs[i] with
  | .right => return (stack, .right)
  | .left  => return (stack, .left)
  | .incr  => return (stack, .incr)
  | .decr  => return (stack, .decr)
  | .out   => return (stack, .out)
  | .in    => return (stack, .in)
  | .fwd () => do
    -- get next .bwd
    match (instrs.drop i).findFinIdx? (· = .bwd ()) with
    | none => throw "No matching `]`"
    | some j =>
      let bwdIdx : Fin instrs.size := Fin.mk (i + j) <| calc (i.val + j)
        _ < i.val + (instrs.drop i).size := Nat.add_lt_add_left j.is_lt _
        _ = instrs.size := by simp
      return (i :: stack, .fwd bwdIdx.succ')
  | .bwd () =>
    match stack with
    | [] => throw "No matching `[`"
    | j :: stack' =>
      return (stack', .bwd j)

def computeInstructionAddrs (instrs : Array (Instruction Unit)) : Except String Program :=
  letI n := instrs.size
  let rec aux (i : Fin (n + 1)) (stack : List (Fin n)) (acc : Vector (Instruction (Fin n)) i) : Except String $ Vector (Instruction (Fin n)) n :=
    if h : i = n then
      if stack.isEmpty then
        return cast (by simp [h]) acc
      else throw ""
    else do
      let (stack', nextInstr) ← computeInstructionAddr instrs stack ⟨i, by omega⟩
      let i' : Fin (n + 1) := ⟨i + 1, by omega⟩
      aux i' stack' (acc.push nextInstr)
  termination_by instrs.size - i

  aux 0 [] #v[]
    <&> Program.mk instrs.size

def parse? (chars : Array Char) : Except String Program := do
  let instrs := chars.filterMap Instruction.parse?
  sorry
  -- TODO
  -- if h : prog.size = instrs.size then
  --   return ⟨instrs.size, prog, h⟩
  -- else unreachable!
  -- let ⟨prog, stack⟩ ← chars
  --   |>.mapFinIdx (fun i c hi => (c, Fin.mk i hi))
  --   |>.foldlM (init := ⟨.empty, []⟩)
  --     fun acc (c, i) => ParseState.next? acc c i

  -- match stack with
  -- | [] => return prog
  -- | (fwdLoc, _) :: _ => throw (.noMatchingBwd fwdLoc)
