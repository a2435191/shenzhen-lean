/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `ReadWrite δ α`
-- `δ`: type of data, like `Integer` or `SimpleIOData`
inductive ReadWrite (δ : Type) : Type v → Type _
| pure (a : α)                      : ReadWrite δ α
| write (d : δ) (a : α)             : ReadWrite δ α
| read (next : ReadWrite δ (δ → α)) : ReadWrite δ α

namespace ReadWrite

def map (f : α → β) : ReadWrite δ α → ReadWrite δ β
  | .pure a => .pure (f a)
  | .write d a => .write d (f a)
  | .read next => .read <| map (f ∘ ·) next

@[simp]
theorem sizeOf_map_eq_sizeOf {f : α → β} {x : ReadWrite δ α} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β <;> simp_all [map]

def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

def writeIfNotAlreadyWritten (toWrite : δ) : ReadWrite δ α → ReadWrite δ α
  | .pure a => .write toWrite a
  | .write written a => .write written a
  | .read next => .read (writeIfNotAlreadyWritten toWrite next)

-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`.
def seq (mf : ReadWrite δ (α → β)) (ma : Unit → ReadWrite δ α) : ReadWrite δ β :=
  match mf with
  | .pure f => map f (ma ())
  | .write d f => writeIfNotAlreadyWritten d (map f (ma ()))
  | .read nextF => .read (seq (map Function.swap nextF) ma)
termination_by sizeOf mf

instance : Applicative (ReadWrite δ) where
  pure := pure
  map := map
  seq := seq

/-- The fundamental property of `writeIfNotAlreadyWritten`. -/
theorem writeIfNotAlreadyWritten_idempotent {x : ReadWrite δ α}
    : writeIfNotAlreadyWritten d' (writeIfNotAlreadyWritten d x) = writeIfNotAlreadyWritten d x := by
  match x with
  | .pure a | .write d a => rfl
  | .read next =>
    simp only [writeIfNotAlreadyWritten, read.injEq]
    apply writeIfNotAlreadyWritten_idempotent

instance : LawfulApplicative (ReadWrite δ) where
  map_const := rfl
  id_map := sorry
  seqLeft_eq a b := rfl
  seqRight_eq a b := rfl
  pure_seq := sorry
  map_pure := sorry
  seq_pure := sorry
  seq_assoc := sorry
