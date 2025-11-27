/-! NYT Pips game solver -/

def n := 7

structure Domino where
  fst : Fin n
  snd : Fin n
  order : fst ≤ snd := by decide

inductive Constraint (number equal notEqual greaterThan lessThan : Nat)
| num : Fin number → Constraint ..
| eq  : Fin equal → Constraint ..
| ne  : Fin notEqual → Constraint ..
| gt  : Fin greaterThan → Constraint ..
| lt  : Fin lessThan → Constraint ..
| empty
| invalid

def Constraint.valid : Constraint number equal notEqual greaterThan lessThan → Bool
| .invalid => false
| _ => true

abbrev Grid (w h : Nat) (α : Type) :=
  Vector (Vector α w) h

structure Game (w h : Nat) where
  number : Nat
  numberValues : Vector Nat number
  equal : Nat
  notEqual : Nat
  greaterThan : Nat
  greaterThanValues : Vector Nat greaterThan
  lessThan : Nat
  lessThanValues : Vector Nat lessThan
  board : Grid w h $ Constraint number equal notEqual greaterThan lessThan

def Game.dominoPositions : Game w h → Grid w h Bool
| { board, .. } => board.map (Vector.map Constraint.valid)

open Constraint in
def medium : Game 5 5 where
  number := 2
  numberValues := #v[9, 27]
  equal := 1
  notEqual := 0
  greaterThan := 1
  greaterThanValues := #v[4]
  lessThan := 1
  lessThanValues := #v[2]
  board := #v[
    #v[invalid, invalid, num 0, lt 0,  invalid],
    #v[invalid, empty,   num 0, lt 0,  empty],
    #v[empty,   eq 0,    num 0, num 1, gt 0],
    #v[invalid, eq 0,    num 1, num 1, num 1],
    #v[invalid, eq 0,    eq 0,  num 1, invalid]]


inductive Direction | n | e | s | w

def Grid.fill (w h : Nat) (a : α) : Grid w h α :=
  Vector.replicate h (Vector.replicate w a)

def tilings (canPlace : Grid w h Bool) : List (Grid w h (Option Direction)) :=
  if hyp : w > 0 ∧ h > 0 then
    go ⟨w - 1, Nat.pred_lt_self hyp.left⟩
       ⟨h - 1, Nat.pred_lt_self hyp.right⟩
       (Grid.fill _ _ none)
  else []
where
  go (x : Fin w) (y : Fin h) (placedSoFar : Grid w h (Option Direction)) :=
    match x, y with
    | ⟨0, _⟩, ⟨0, _⟩ => []
    | ⟨1, _⟩, ⟨0, _⟩


#check Fin.land
