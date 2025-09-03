import Shenzhen.Instruction

/-- `XBusEffects` wraps values of type `α` in a functor that
  records pin read and write actions within a chip with XBus pins.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`). -/
inductive XBusEffects (ξ : Type u) (δ : Type v) (α : Type w)
/-- Wrap a value in `XBusEffects` without signaling the need for a read or write. -/
| pure : α → XBusEffects ξ δ α
/-- `write pin d next` represents some data `d` being written to
  XBus pin `pin`. Then `next` is the state after performing the write. -/
| write (pin : ξ) (d : δ) (next : α)
/-- `read pin next` represents a computation delayed until a value `d`
  from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| read (pin : ξ) (next : δ → XBusEffects ξ δ α)
/-- `peek pin next` represents a computation delayed until the value
  from XBus pin `pin` is known; then `next` is the state after performing the peek.
  But unlike `read` the next state cannot use the value read from `pin`.
  This is used to implement the `slx` operation. -/
| peek (pin : ξ) (next : α)
deriving Inhabited

namespace XBusEffects

def bind (mx : XBusEffects ξ δ α) (f : α → XBusEffects ξ δ β) : XBusEffects ξ δ β :=
  match mx with
  | .pure a => f a
  | .write pin d next =>
    match f next with
    | .pure b => .write pin d b
    | next' => next' -- Note: this is not a lawful monad if we do something impure after we write.
  | .read pin next => .read pin fun d => bind (next d) f
  | .peek pin next =>
    match f next with
    | .pure b => .peek pin b
    | next' => next' -- Note: this is not a lawful monad if we do something impure after we peek.

instance : Monad (XBusEffects ξ δ) where
  pure := pure
  bind := bind

@[inline] def isPure : XBusEffects ξ δ α → Bool
| .pure _ => true
| _ => false

instance [ToString ξ] [ToString δ] [ToString α] [OfNat δ 37] : ToString (XBusEffects ξ δ α) :=
  ⟨go⟩
where
  go
  | .pure a => s!".pure ({toString a})"
  | .write pin d next => s!".write {pin} {d} ({next})"
  | .read pin next => s!".read {pin} (fun | 37 => {go (next 37)} | ⋯)"
  | .peek pin next => s!".peek {pin} ({next})"

end XBusEffects

-- def XBusEffectsT (ξ : Type u) (δ : Type v) (m : Type w → Type x) (α : Type w) :=
--   XBusEffects ξ δ (m α)

-- def XBusEffectsT' (ξ : Type u) (δ : Type v) (m : Type max u v w → Type x) (α : Type w) :=
--   m (XBusEffects ξ δ α)

-- def XBusEffectsT'.mk (x : m (XBusEffects ξ δ α)) : XBusEffectsT' ξ δ m α :=
--   x


-- namespace XBusEffectsT

-- abbrev M := ReaderM String
-- protected def bind' (ma : XBusEffectsT ξ δ M α) (f : α → XBusEffectsT ξ δ M β) : XBusEffectsT ξ δ M β :=
--   match ma with
--   | XBusEffects.pure a =>
--     .pure fun s =>
--       let := f (a s)
--       sorry
--   | XBusEffects.write pin d next =>
--     sorry
--     -- .write pin d
--   | XBusEffects.read pin next =>
--     sorry
--     -- .read pin fun d => XBusEffectsT.bind' (next d) f
--   | XBusEffects.peek pin next => sorry

-- -- def bind.go {ξ : Type u} {δ : Type v} {α : Type w}

-- protected def pure [Pure m] : α → XBusEffectsT ξ δ m α
-- | a => XBusEffects.pure (Pure.pure a)


-- instance [Monad m] : Monad (XBusEffectsT ξ δ m) where
--   pure := .pure
--   bind := .bind

-- end XBusEffectsT
