import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `BlockingEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.
  - `τ` is the type of the *t*ick state, i.e. the state that simple I/O operations
        can modify in the middle of an instruction's execution. -/
inductive BlockingEffects (ξ : Type u) (ι : Type v) (τ : Type w) (α : Type x)
/-- Just return a value immediately, without doing any effects. -/
| pure (a : α)
/-- `xBusRead pin next` represents a computation delayed until a value `d`
  from `pin` can be read; then `next d` is the result of the computation. -/
| xBusRead (pin : ξ) (next : Integer → BlockingEffects ξ ι τ α)
/-- `d` is some data to be thereafter written out of `outPin`, and `next ()` is returned after the write. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : Unit → BlockingEffects ξ ι τ α)
/-- `poll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives; then `next ()` is the result thereafter.
  This is used to implement the `slx` operation. -/
| poll (pin : ξ) (next : Unit → BlockingEffects ξ ι τ α)
| simpleIORead (pin : ι) (nextTickState : τ → τ) (next : SimpleIOData → BlockingEffects ξ ι τ α)
| simpleIOWrite (outPin : ι) (nextTickState : τ → τ) (d : SimpleIOData) (next : Unit → BlockingEffects ξ ι τ α)
/-- Wait for `ticks` ticks. -/
| sleep (ticks : Nat) (h : ticks ≠ 0) (next : Unit → BlockingEffects ξ ι τ α)

namespace BlockingEffects

instance [Inhabited α] : Inhabited (BlockingEffects ξ ι τ α) :=
  ⟨pure default⟩

-- @[simp]
-- def map (f : α → β) : BlockingEffects ξ ι τ α → BlockingEffects ξ ι τ β
-- | .pure a => pure (f a)
-- | .xBusRead p next => .xBusRead p fun d => map f (next d)
-- | .simpleIORead p next => .simpleIORead p fun d => map f (next d)
-- | .xBusWrite p d next => .xBusWrite p d fun () => map f (next ())
-- | .simpleIOWrite p d next => .simpleIOWrite p d fun () => map f (next ())
-- | .poll p next => .poll p fun () => map f (next ())
-- | .sleep ticks h next => .sleep ticks h fun () => map f (next ())

instance : Pure (BlockingEffects ξ ι τ ) where
  pure := .pure

-- instance : Functor (BlockingEffects ξ ι τ) where
--   map := map

-- @[simp]
-- def seq (mf : BlockingEffects ξ ι (α → β)) (mx : Unit → BlockingEffects ξ ι α) : BlockingEffects ξ ι β :=
--   match mf with
--   | pure f => f <$> mx ()
--   | .xBusRead t p next => .read t p fun d => seq (next d) mx
--   | .write t p d next => .write t p d fun () => seq (next ()) mx
--   | .poll t p next => .poll t p fun () => seq (next ()) mx
--   | .sleep t ticks h next => .sleep t ticks h fun () => seq (next ()) mx

-- instance : Seq (BlockingEffects ξ ι) where
--   seq := seq

/-- You really should not be using data-dependent effects, as none of the instructions require them.
  But creating this `Monad` instance allows the use of `do` notation. -/
@[simp]
def bind (mx : BlockingEffects ξ ι τ α) (f : α → BlockingEffects ξ ι τ β) : BlockingEffects ξ ι τ β :=
  match mx with
  | pure a => f a
  | .xBusRead p next => .xBusRead p fun d => bind (next d) f
  | .simpleIORead p t next => .simpleIORead p t fun d => bind (next d) f
  | .xBusWrite p d next => .xBusWrite p d fun () => bind (next ()) f
  | .simpleIOWrite p t d next => .simpleIOWrite p t d fun () => bind (next ()) f
  | .poll p next => .poll p fun () => bind (next ()) f
  | .sleep ticks h next => .sleep ticks h fun () => bind (next ()) f

instance : Monad (BlockingEffects ξ ι τ) where
  bind := bind

section

-- TODO: make this local
attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

theorem id_map (x : BlockingEffects ξ ι τ α) : id <$> x = x := by
  induction x <;> try rfl
  all_goals
    simp; rename_i ih; funext; apply ih

theorem bind_pure_comp (f : α → β) (x : BlockingEffects ξ ι τ α) : x >>= (fun a => pure (f a)) = f <$> x := by
  induction x
  all_goals
    simp <;> rename_i ih <;> funext <;> apply ih

instance : LawfulMonad (BlockingEffects ξ τ ι) where
  map_const := rfl
  id_map := id_map
  seqLeft_eq x y := by
    simp [SeqLeft.seqLeft]
    induction x
    all_goals
      first | apply bind_pure_comp | rename_i ih; funext; simp [ih]
  seqRight_eq x y := by
    simp [SeqRight.seqRight]
    induction x
    all_goals
      first | symm; apply id_map | rename_i ih; funext; simp [ih]
  pure_seq f x := by simp [Seq.seq]
  bind_pure_comp := bind_pure_comp
  bind_map f x := by
    induction f <;> simp <;> (rename_i ih; funext; apply ih)
  pure_bind := by simp
  bind_assoc x f g := by
    induction x <;> simp <;> (rename_i ih; funext; apply ih)

end

def tickSleep : BlockingEffects ξ ι τ α → BlockingEffects ξ ι τ α
| .sleep 1 _ next => next ()
| .sleep (k + 2) _ next => .sleep (k + 1) (by simp) next
| fx => fx

end BlockingEffects
