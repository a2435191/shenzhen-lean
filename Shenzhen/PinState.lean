import Shenzhen.Instruction

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/-- `PinState.XBus` wraps values of type `α` in a functor that
  records pin read and write actions within a chip with XBus pins.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`). -/
inductive PinState.XBus (ξ : Type u) (δ : Type v) (α : Type x)
/-- Wrap a value in `PinState.XBus` without signaling the need for a read or write. -/
| pure : α → XBus ξ δ α
/-- `writeXBus pin d next` represents some data `d` being written to
  XBus pin `pin`. Then `next` is the state after performing the write. -/
| writeXBus (pin : ξ) (d : δ) (next : α)
/-- `readXBus pin next` represents a computation delayed until a value `d`
  from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| readXBus (pin : ξ) (next : δ → XBus ξ δ α)
/-- `peekXBus pin next` represents a computation delayed until the value
  from XBus pin `pin` is known; then `next` is the state after performing the peek.
  But unlike `readXBus` the next state cannot use the value read from `pin`.
  This is used to implement the `slx` operation. -/
| peekXBus (pin : ξ) (next : XBus ξ δ α)
deriving Inhabited

namespace PinState.XBus

def bind (mx : XBus ξ δ α) (f : α → XBus ξ δ β) : XBus ξ δ β :=
  match mx with
  | .pure a => f a
  | .writeXBus pin d next =>
    match f next with
    | .pure b => .writeXBus pin d b
    | next' => next' -- Note: this is not a lawful monad instance if we do something impure after we write.
  | .readXBus pin next => .readXBus pin (fun d => bind (next d) f)
  | .peekXBus pin next => .peekXBus pin (bind next f)

instance : Monad (XBus ξ δ) where
  pure := .pure
  bind := bind

instance [ToString ξ] [ToString δ] [ToString α] [OfNat δ 37] : ToString (XBus ξ δ α) :=
  ⟨go⟩
where
  go
  | .pure a => s!".pure ({toString a})"
  | .writeXBus pin d next => s!".writeXBus {pin} {d} ({next})"
  | .readXBus pin next => s!".readXBus {pin} (fun | 37 => {go (next 37)} | ⋯)"
  | .peekXBus pin next => s!".peekXBus {pin} ({go next})"

end XBus

inductive SimpleIO (ι : Type u) (δ : Type v) (α : Type w)
| pure : α → SimpleIO ι δ α
| writeSimpleIO (pin : ι) (d : δ) (next : α)
| readSimpleIO (pin : ι) (next : δ → SimpleIO ι δ α)

-- def bind (mx : SimpleIO ι δ α) (f : α → SimpleIO ι δ β) : SimpleIO ι δ β :=
--   match mx with
--   | .pure a => f a
--   | .writeSimpleIO pin d next => .writeSimpleIO pin d (bind next f)
--   |

-- instance : Monad (SimpleIO ι δ) where
--   pure := .pure
--   bind := bind

@[specialize] def SimpleIO.resolve (onWrite : ι → δ → α → α) (onRead : ι → α → α) (prevPinValues : ι → δ) : SimpleIO ι δ α → α :=
  go
where
  @[inline] go
  | .pure a => a
  | .writeSimpleIO pin d next => onWrite pin d next
  | .readSimpleIO pin next => onRead pin (go (next (prevPinValues pin)))

end PinState

abbrev PinState (ξ : Type u) (δ : Type v) (ι : Type w) (ε : Type x) (α : Type y) :=
  PinState.XBus ξ δ (PinState.SimpleIO ι ε α)
