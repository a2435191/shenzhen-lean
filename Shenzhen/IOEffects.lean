import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) (α : Type x)
/-- Just return a value immediately, without doing any effects. -/
| pure (a : α)
/-- `xBusRead pin next` represents a computation delayed until a value `d`
  from `pin` can be read; then `next d` is the result of the computation. -/
| xBusRead (pin : ξ) (next : Integer → IOEffects ξ ι α)
/-- `d` is some data to be thereafter written out of `outPin`, and `next ()` is returned after the write. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : Unit → IOEffects ξ ι α)
/-- `xBusPoll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives (but without consuming the value);
  then `next ()` is the result thereafter.
  This is used to implement the `slx` instruction. -/
| xBusPoll (pin : ξ) (next : Unit → IOEffects ξ ι α)
| simpleIORead (pin : ι) (next : SimpleIOData → IOEffects ξ ι α)
| simpleIOWrite (outPin : ι) (d : SimpleIOData) (next : Unit → IOEffects ξ ι α)
/-- Wait for `n` time units. -/
| sleep (n : Nat) (h : n ≠ 0) (next : Unit → IOEffects ξ ι α)

namespace IOEffects

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨pure default⟩

instance : Pure (IOEffects ξ ι) where
  pure := .pure

@[simp]
def bind (mx : IOEffects ξ ι α) (f : α → IOEffects ξ ι β) : IOEffects ξ ι β :=
  match mx with
  | pure a => f a
  | .xBusRead p next => .xBusRead p fun d => bind (next d) f
  | .simpleIORead p next => .simpleIORead p fun d => bind (next d) f
  | .xBusWrite p d next => .xBusWrite p d fun () => bind (next ()) f
  | .simpleIOWrite p d next => .simpleIOWrite p d fun () => bind (next ()) f
  | xBusPoll p next => xBusPoll p fun () => bind (next ()) f
  | .sleep n h next => .sleep n h fun () => bind (next ()) f

instance : Monad (IOEffects ξ ι) where
  bind := bind

section

-- TODO: make this local
attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

theorem id_map (x : IOEffects ξ ι α) : id <$> x = x := by
  induction x <;> try rfl
  all_goals
    simp; rename_i ih; funext; apply ih

theorem bind_pure_comp (f : α → β) (x : IOEffects ξ ι α) : x >>= (fun a => pure (f a)) = f <$> x := by
  induction x
  all_goals
    simp <;> rename_i ih <;> funext <;> apply ih

instance : LawfulMonad (IOEffects ξ ι) where
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

abbrev isSleep : IOEffects ξ ι α → Bool
| .sleep .. => true
| _ => false

def sleepOne (fx : IOEffects ξ ι α) (h : fx.isSleep = true) : IOEffects ξ ι α :=
  match fx with
  | .sleep 1 _ next => next ()
  | .sleep (k + 2) _ next => .sleep (k + 1) (Nat.succ_ne_zero _) next


end IOEffects
