/-- `StateAT σ m α` is like `StateT σ m α`, except it keeps the state outside the monad.
  It is equivalent to `σ → m α × σ`. Note that this is not a lawful monad, but just a lawful `Applicative` (which the `A` stands for). -/
@[expose]
def StateAT (σ : Type u) (m : Type u → Type u) (α : Type u) : Type u :=
  StateM σ (m α)

namespace StateAT

@[simp]
protected def mk (x : σ → m α × σ) : StateAT σ m α := x

protected def pure [Pure m] (a : α) : StateAT σ m α :=
  show StateM σ (m α) from do
  Pure.pure (Pure.pure a)

@[simp]
theorem pure_eq [Pure m] : StateAT.pure (m := m) (σ := σ) a = fun s => (pure a, s) :=
  rfl

protected def seq [Seq m] (f : StateAT σ m (α → β)) (x : Unit → StateAT σ m α) : StateAT σ m β :=
  fun s =>
    let (mf, sf) := f s
    let (ma, sa) := x () sf
    (mf <*> ma, sa)

@[simp]
theorem seq_eq [Seq m] : StateAT.seq (m := m) (σ := σ) f x = fun s => ((f s).1 <*> (x () (f s).2).1, (x () (f s).2).2) :=
  rfl

protected def map [Functor m] (f : α → β) (x : StateAT σ m α) : StateAT σ m β :=
  fun s =>
    let (ma, s') := x s
    (f <$> ma, s')

@[simp]
theorem map_eq [Functor m] : StateAT.map (m := m) (σ := σ) f x = fun s => (f <$> (x s).1, (x s).2) :=
  rfl

instance [Applicative m] : Applicative (StateAT σ m) where
  pure := .pure
  seq := .seq
  map := .map

instance [Applicative m] [LawfulApplicative m] : LawfulApplicative (StateAT σ m) where
  map_const := rfl
  id_map x := by
    funext s
    simp [Functor.map]
    rfl
  pure_seq g x := by
    funext s
    simp [Functor.map, Seq.seq, pure, pure_seq]
  seq_pure g x := by
    funext s
    simp [Seq.seq, Functor.map, pure]
  map_pure g x := by
    funext s
    simp [Functor.map, pure]
  seq_assoc x g h := by
    funext s
    simp [Seq.seq, Functor.map, seq_assoc]
  seqLeft_eq x y := by
    funext s
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map]
  seqRight_eq x y := by
    funext s
    simp [SeqRight.seqRight, Seq.seq, Functor.map]

-- I don't think any implementation of `bind` will respect `bind_map`, `pure_bind`, and `bind_assoc`
-- So this remains an applicative
