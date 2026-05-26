/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `δ`: type of data, like `Integer` or `SimpleIOData`
inductive ReadWrite (δ : Type u) (α : Type v)
| end (write? : Option δ) (a : α)
| read (next : δ → ReadWrite δ α)

namespace ReadWrite

def pure : α → ReadWrite δ α
| a => .end none a

def writeIfNotAlreadyWritten (toWrite : δ) : ReadWrite δ α → ReadWrite δ α
| .end none a => .end (some toWrite) a
| .end (some written) a => .end (some written) a
| .read next => .read fun toRead => writeIfNotAlreadyWritten toWrite (next toRead)

def bind : ReadWrite δ α → (α → ReadWrite δ β) → ReadWrite δ β
| .end none a, f => f a
| .end (some d) a, f => writeIfNotAlreadyWritten d (f a)
| .read next, f => .read fun toRead => bind (next toRead) f

instance : Monad (ReadWrite δ) where
  pure := .pure
  bind := .bind

/-- The fundamental property of `writeIfNotAlreadyWritten`. -/
theorem writeIfNotAlreadyWritten_idempotent {x : ReadWrite δ α}
    : writeIfNotAlreadyWritten d' (writeIfNotAlreadyWritten d x) = writeIfNotAlreadyWritten d x := by
  match x with
  | .end none a | .end (some d) a => rfl
  | .read next =>
    simp [writeIfNotAlreadyWritten]
    funext toRead
    apply writeIfNotAlreadyWritten_idempotent

theorem writeIfNotAlreadyWritten_bind_assoc {x : ReadWrite δ α} {f : α → ReadWrite δ β}
    : writeIfNotAlreadyWritten toWrite x >>= f = writeIfNotAlreadyWritten toWrite (x >>= f) :=
  match x with
  | .end none a => rfl
  | .end (some d) a => by
    simp [Bind.bind, ReadWrite.bind, writeIfNotAlreadyWritten]
    symm
    exact writeIfNotAlreadyWritten_idempotent
  | .read next => by
    simp [Bind.bind, ReadWrite.bind, writeIfNotAlreadyWritten]
    funext toRead
    apply writeIfNotAlreadyWritten_bind_assoc

instance : LawfulMonad (ReadWrite δ) :=
  LawfulMonad.mk' _ @id_map @pure_bind @bind_assoc
where
  id_map {α}
  | .end none a | .end (some d) a => rfl
  | .read next => by
    simp [Functor.map, ReadWrite.bind]
    funext d
    apply id_map
  pure_bind {α β} a f := rfl
  bind_assoc {α β γ} x f g :=
    match x with
    | .end none a => rfl
    | .end (some d) a => by
      simp [Bind.bind, bind]
      exact writeIfNotAlreadyWritten_bind_assoc
    | .read next => by
      simp [Bind.bind, ReadWrite.bind]
      funext toRead
      apply bind_assoc
