import Shenzhen.Instruction

/-- `IP m` is the type of an instruction pointer for an `MC4000` with `m` instructions.
  Chips can have zero instructions, so `IP m` is equivalent to `if m = 0 then Unit else Fin m`, but
  this way we get `Repr` for free and nicer pattern-matching. -/
inductive IP : Nat → Type
| none : IP 0
| ofFin : Fin m → IP m
deriving Repr

namespace IP

instance : ReprAtom (IP 0) where

def toFin (h : m ≠ 0) : IP m → Fin m
| .none => False.elim (h rfl)
| .ofFin x => x

def mk' (ofNonZero : (m : Nat) → m ≠ 0 → Fin m) {m} : IP m :=
  match m with
  | 0 => .none
  | k + 1 => .ofFin <| ofNonZero (k + 1) (by simp)

/-- `(0 : Fin m)` unless `m = 0` -/
def null : IP m :=
  .mk' fun _ h => ⟨0, Nat.zero_lt_of_ne_zero h⟩

instance : Inhabited (IP m) where
  default := .null

instance : Coe (Fin m) (IP m) := ⟨.ofFin⟩

/-- Find the index `i` of the next instruction **greater than** `curr` that
  is enabled according to `flags[i]` and `cond`, looping back around from
  `i = m - 1` to `i = 0` if necessary. `none` if no such index exists.
  (We don't use the `IP` constructor because we want to be able to return `none`
  for `m > 0`.) -/
def nextIP {m} (flags : Vector ConditionalFlag m)
    (curr : Fin m) (cond : ConditionalState m) : Option (Fin m) :=
  let start := curr.succ' -- where we start looking
  let foundOffset := Fin.find? fun offset =>
    let i := offset + start
    match flags[i] with
    | .none => true
    | .pos => cond.posEnabled
    | .neg => cond.negEnabled
    | .once => !cond.hasRun[i]
  foundOffset <&> (· + start)

end IP
