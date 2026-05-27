import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) : Type x → Type _
/-- Just return a value immediately, without doing any effects.
  This is a final state (no more effects after this point, i.e.
  no constructor parameters of type `IOEffects`). -/
| pure (a : α)                                                     : IOEffects ξ ι α
/-- Read a value (possibly blocking) from pin `pin`, and then do
  something with it. That function
  (the `Integer → α` part) is wrapped in another `IOEffects`
  representing the next state. -/
| xBusRead (pin : ξ) (next : IOEffects ξ ι (Integer → α))          : IOEffects ξ ι α
/-- `d` is some data to be thereafter written out of `outPin`
  (also blocking), and `next` is the state immediately after
  the write.
  Note that this is a final state since `next` is pure. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : α)                  : IOEffects ξ ι α
/-- Wait until the value from XBus pin `pin` arrives,but don't
  consume the value). Then `next` is the state after the value
  arrives. This is used to implement the `slx` instruction.

  Note that this is a final state. -/
| xBusPoll (pin : ξ) (next : α)                                    : IOEffects ξ ι α
/-- Like `xBusRead` but non-blocking. -/
| simpleIORead (pin : ι) (next : IOEffects ξ ι (SimpleIOData → α)) : IOEffects ξ ι α
/-- Like `xBusWrite` but non-blocking. Note that this is a
  final state. -/
| simpleIOWrite (outPin : ι) (d : SimpleIOData) (next : α)         : IOEffects ξ ι α
/-- Wait for `n` time units. `n ≠ 0` because `pure` already exists.
  `next` is the (pure) state after we are done waiting, so
  this is a final state. -/
| sleep (n : Nat) (h : n ≠ 0) (next : α)                           : IOEffects ξ ι α

namespace IOEffects

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨pure default⟩

instance : Pure (IOEffects ξ ι) where
  pure := .pure

-- @[simp]
-- def bind (mx : IOEffects ξ ι α) (f : α → IOEffects ξ ι β) : IOEffects ξ ι β :=
--   match mx with
--   | pure a => f a
--   | .xBusRead p next => .xBusRead p fun d => bind (next d) f
--   | .simpleIORead p next => .simpleIORead p fun d => bind (next d) f
--   | .xBusWrite p d next => .xBusWrite p d fun () => bind (next ()) f
--   | .simpleIOWrite p d next => .simpleIOWrite p d fun () => bind (next ()) f
--   | xBusPoll p next => xBusPoll p fun () => bind (next ()) f
--   | .sleep n h next => .sleep n h fun () => bind (next ()) f

-- instance : Monad (IOEffects ξ ι) where
--   bind := bind

-- section

-- -- TODO: make this local
-- attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

-- theorem id_map (x : IOEffects ξ ι α) : id <$> x = x := by
--   induction x <;> try rfl
--   all_goals
--     simp; rename_i ih; funext; apply ih

-- theorem bind_pure_comp (f : α → β) (x : IOEffects ξ ι α) : x >>= (fun a => pure (f a)) = f <$> x := by
--   induction x
--   all_goals
--     simp <;> rename_i ih <;> funext <;> apply ih

-- instance : LawfulMonad (IOEffects ξ ι) where
--   map_const := rfl
--   id_map := id_map
--   seqLeft_eq x y := by
--     simp [SeqLeft.seqLeft]
--     induction x
--     all_goals
--       first | apply bind_pure_comp | rename_i ih; funext; simp [ih]
--   seqRight_eq x y := by
--     simp [SeqRight.seqRight]
--     induction x
--     all_goals
--       first | symm; apply id_map | rename_i ih; funext; simp [ih]
--   pure_seq f x := by simp [Seq.seq]
--   bind_pure_comp := bind_pure_comp
--   bind_map f x := by
--     induction f <;> simp <;> (rename_i ih; funext; apply ih)
--   pure_bind := by simp
--   bind_assoc x f g := by
--     induction x <;> simp <;> (rename_i ih; funext; apply ih)

-- end

-- /-- In `sleep` or `xBusPoll` state -/
-- abbrev isSleep : IOEffects ξ ι α → Bool
-- | .sleep .. | .xBusPoll .. => true
-- | _ => false

-- /-- Advance `.sleep` states by one time unit. Leave `.xBusPoll` states alone. -/
-- def advanceSleep (fx : IOEffects ξ ι α) (h : fx.isSleep = true) : IOEffects ξ ι α :=
--   match fx with
--   | .xBusPoll .. => fx
--   | .sleep 1 _ next => next ()
--   | .sleep (k + 2) _ next => .sleep (k + 1) (Nat.succ_ne_zero _) next

-- end IOEffects
