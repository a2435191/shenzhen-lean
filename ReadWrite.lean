-- inductive Read (δ : Type u) (α : Type v)
-- | pure : α → Read δ α
-- | read (next : δ → Read δ α)

-- def Read.bind : Read δ α → (α → Read δ β) → Read δ β
-- | .pure a, f => f a
-- | .read next, f => .read fun d => bind (next d) f

-- instance : Monad (Read δ) where
--   pure := .pure
--   bind := .bind

-- -- Equivalent to `α × Option δ`
-- structure Write (δ : Type u) (α : Type v) where
--   pure : α
--   written : Option δ

-- def ReadWrite (δ : Type u) (α : Type v) :=
--   Read δ (Write δ α)

-- def ReadWrite.pure : α → ReadWrite δ α
-- | a => Read.pure ⟨a, none⟩

-- def ReadWrite.bind : ReadWrite δ α → (α → ReadWrite δ β) → ReadWrite δ β
-- | Read.pure ⟨a, _⟩, f => f a -- possibly overwrite the previous written value (if `written` was `some`)
-- | Read.read next, f => Read.read fun d => bind (next d) f



-- | pure : α → Write δ α
-- -- Note that `next` is not `Unit → Write δ α`
-- -- because we want there to be at most one write
-- | write (d : δ) (next : Unit → α)
-- | write (data : δ) (next : Unit → ReadWrite δ α)

inductive ReadWrite (δ : Type u) (α : Type v)
| end (write? : Option δ) (a : α)
| read (next : δ → ReadWrite δ α)

namespace ReadWrite

def pure : α → ReadWrite δ α
| a => .end none a

def write : δ → α → ReadWrite δ α
| d, a => .end (some d) a

def write' : δ → ReadWrite δ Unit
| d => write d ()

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
