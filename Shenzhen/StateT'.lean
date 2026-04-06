@[expose]
def StateT' (σ : Type u) (m : Type u → Type u) (α : Type u) : Type u :=
  StateM σ (m α)

namespace StateT'
variable {m : Type u → Type u}

protected def pure [Pure m] (a : α) : StateT' σ m α :=
  show StateM σ (m α) from do
  Pure.pure (Pure.pure a)

@[simp]
theorem pure_eq [Pure m] : StateT'.pure (m := m) (σ := σ) a = fun s => (pure a, s) :=
  rfl

protected def seq [Seq m] (f : StateT' σ m (α → β)) (x : Unit → StateT' σ m α) : StateT' σ m β :=
  fun s =>
    let (mf, sf) := f s
    let (ma, sa) := x () sf
    (mf <*> ma, sa)

@[simp]
theorem seq_eq [Seq m] : StateT'.seq (m := m) (σ := σ) f x = fun s => ((f s).1 <*> (x () (f s).2).1, (x () (f s).2).2) :=
  rfl

protected def map [Functor m] (f : α → β) (x : StateT' σ m α) : StateT' σ m β :=
  fun s =>
    let (ma, s') := x s
    (f <$> ma, s')

@[simp]
theorem map_eq [Functor m] : StateT'.map (m := m) (σ := σ) f x = fun s => (f <$> (x s).1, (x s).2) :=
  rfl

instance [Applicative m] : Applicative (StateT' σ m) where
  pure := .pure
  seq := .seq
  map := .map

instance [Applicative m] [LawfulApplicative m] : LawfulApplicative (StateT' σ m) where
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

-- TODO: Monad?
