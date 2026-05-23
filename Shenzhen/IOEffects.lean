import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) : (α : Type x) → Type _
/-- Just return a value immediately, without doing any effects. -/
| pure : α → IOEffects _ _ α
/-- `xBusRead pin next` represents a computation delayed until a value `d`
  from `pin` can be read; then `next d` is the result of the computation. -/
| xBusRead (pin : ξ) (next : IOEffects ξ ι (Integer → α)) : IOEffects _ _ α
/-- `d` is some data to be thereafter written out of `outPin`, and `next ()` is returned after the write. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : IOEffects ξ ι α) : IOEffects _ _ α
/-- `xBusPoll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives; then `next ()` is the result thereafter.
  This is used to implement the `slx` operation. -/
| xBusPoll (pin : ξ) (next : IOEffects ξ ι α) : IOEffects _ _ α
| simpleIORead (pin : ι) (next : IOEffects ξ ι (SimpleIOData → α)) : IOEffects _ _ α
| simpleIOWrite (outPin : ι) (d : SimpleIOData) (next : IOEffects ξ ι α) : IOEffects _ _ α
/-- Wait for `n` time units. -/
| sleep (n : Nat) (h : n ≠ 0) (next : IOEffects ξ ι α) : IOEffects _ _ α

namespace IOEffects

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨pure default⟩

instance : Pure (IOEffects ξ ι) where
  pure := pure

@[simp]
def map (f : α → β) : IOEffects ξ ι α → IOEffects ξ ι β
  | .pure a => .pure (f a)
  | .xBusRead pin next => .xBusRead pin (map (f ∘ ·) next)
  | .xBusWrite pin d next => .xBusWrite pin d (map f next)
  | .xBusPoll pin next => .xBusPoll pin (map f next)
  | .simpleIORead pin next => .simpleIORead pin (map (f ∘ ·) next)
  | .simpleIOWrite pin d next => .simpleIOWrite pin d (map f next)
  | .sleep n h next => .sleep n h (map f next)

instance : Functor (IOEffects ξ ι) where
  map := map

-- Just needed for termination proof below
@[simp]
def size : IOEffects ξ ι α → Nat
  | .pure _ => 1
  | .xBusRead _ next | .xBusWrite _ _ next | .xBusPoll _ next
  | .simpleIORead _ next | .simpleIOWrite _ _ next
  | .sleep _ _ next => 1 + size next

@[simp]
theorem size_map {α} {x : IOEffects ξ ι α} {β} {f : α → β} : size (f <$> x) = size x := by
  cases x
  all_goals first | rfl | exact congrArg _ size_map

@[simp]
def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

@[simp]
def seq (mf : IOEffects ξ ι (α → β)) (mx : Unit → IOEffects ξ ι α) : IOEffects ξ ι β :=
  match mf with
  | .pure f => f <$> mx ()
  | .xBusRead pin next => .xBusRead pin (seq (Function.swap <$> next) mx)
  | .xBusWrite pin d next => .xBusWrite pin d (seq next mx)
  | .xBusPoll pin next => .xBusPoll pin (seq next mx)
  | .simpleIORead pin next => .simpleIORead pin (seq (Function.swap <$> next) mx)
  | .simpleIOWrite pin d next => .simpleIOWrite pin d (seq next mx)
  | .sleep n h next => .sleep n h (seq next mx)
termination_by size mf

instance : Applicative (IOEffects ξ ι) where
  seq := seq

section

-- TODO: make this local
attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

theorem id_map (x : IOEffects ξ ι α) : id <$> x = x := by
  induction x <;> try rfl
  all_goals
    simp; rename_i ih; funext; apply ih

-- theorem seq_pure {α : Type u} {β : Type u} (g : IOEffects ξ ι (α → β)) (a : α) : g <*> Pure.pure a = (fun h => h a) <$> g := by
--   cases g
--   · simp
--   · simp
--     unfold Function.swap Function.comp
--     simp
--     sorry
--   all_goals sorry

-- instance : LawfulApplicative (IOEffects ξ ι) where
--   map_const := rfl
--   id_map := id_map
--   seqLeft_eq x y := rfl
--   seqRight_eq x y := rfl
--   pure_seq f x := by simp
--   map_pure := by simp
--   seq_pure := seq_pure
--   seq_assoc x g h := by
--     induction x
--     · show _ <*> (_ <*> Pure.pure _) = _ <*> Pure.pure _
--       simp only [seq_pure]

--       sorry
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--     · sorry

end

def sleepOne : IOEffects ξ ι α → IOEffects ξ ι α
| .sleep 1 _ next => next
| .sleep (k + 2) _ next => .sleep (k + 1) (Nat.succ_ne_zero _) next
| fx => fx

abbrev isSleep : IOEffects ξ ι α → Bool
| .sleep .. => true
| _ => false

end IOEffects
