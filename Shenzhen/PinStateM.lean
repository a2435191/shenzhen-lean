import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/-- `PinStateM` wraps values of type `α` in a monad that
  records pin read actions within a chip with XBus and simple IO pins.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*O pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`).
  - `ε` is the type of data read over simple IO pins (probably `SimpleIOData`). -/
inductive PinStateM (ξ : Type u) (ι : Type v) (δ : Type w) (ε : Type x) (α : Type y)
/-- Wrap a value in `PinStateM` without signaling the need for a read or write. -/
| pure : α → PinStateM ξ ι δ ε α
/-- `writeXBus pin d` represents some data `d` being written to
  XBus pin `pin`. Then `next` is the state after performing the write. -/
| writeXBus (pin : ξ) (d : δ) (next : PinStateM ξ ι δ ε α)
/-- `writeSimpleIO pin d` represents some data `d` being written to
  simple IO pin `pin`. Then `next` is the state after performing the write. -/
| writeSimpleIO (pin : ι) (d : ε) (next :  PinStateM ξ ι δ ε α)
/-- `readXBus pin next` represents a computation delayed until a value `d`
  from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| readXBus (pin : ξ) (next : δ → PinStateM ξ ι δ ε α)
/-- `readSimpleIO pin next` represents a computation delayed until the value `d`
  from simple IO pin `pin` is known; then `next d` is the result of the computation. -/
| readSimpleIO (pin : ι) (next : ε → PinStateM ξ ι δ ε α)
deriving Inhabited

namespace PinStateM
@[inline] def bind : PinStateM ξ ι δ ε α → (α → PinStateM ξ ι δ ε β) → PinStateM ξ ι δ ε β
| .pure a, f => f a
| .writeXBus pin d next, f => .writeXBus pin d (bind next f)
| .writeSimpleIO pin d next, f => .writeSimpleIO pin d (bind next f)
| .readXBus pin next, f => .readXBus pin (fun d => bind (next d) f)
| .readSimpleIO pin next, f => .readSimpleIO pin (fun d => bind (next d) f)

instance : Monad (PinStateM ξ ι δ ε) where
  pure := PinStateM.pure
  bind := PinStateM.bind

instance : LawfulMonad (PinStateM ξ ι δ ε) :=
  .mk' _ (by intros; rfl) bind_assoc (id_map := id_map)
where
  bind_assoc {α β γ} (x : PinStateM ξ ι δ ε α) (f : α → PinStateM ξ ι δ ε β) (g : β → PinStateM ξ ι δ ε γ) := by
    cases x
    all_goals first
      | rfl
      | simp [Bind.bind, bind]
        funext
        apply bind_assoc
  id_map {α} (x) := by
    cases x
    all_goals first
      | rfl
      | simp [Functor.map, bind]
        try funext d
        apply id_map

@[reducible, inline] def isXBus : PinStateM ξ ι δ ε α → Bool
| .writeXBus .. | .readXBus .. => true
| _ => false

@[simp] theorem isXBus_map_iff {f : α → β} : isXBus (f <$> p) = true ↔ isXBus p := by
  cases p <;> simp [Functor.map, bind]

@[reducible, inline] def isSimpleIO : PinStateM ξ ι δ ε α → Bool
| .writeSimpleIO .. | .readSimpleIO .. => true
| _ => false

@[simp] theorem isSimpleIO_map_eq {f : α → β} : isSimpleIO (f <$> p) = isSimpleIO p := by
  cases p <;> simp [Functor.map, bind]

def sizeOf' [instδ : Fintype δ] [instε : Fintype ε] : PinStateM ξ ι δ ε α → Nat
| .pure _ => 1
| .writeSimpleIO _ _ next | .writeXBus _ _ next =>
  1 + sizeOf' next
| .readSimpleIO _ next =>
  1 + (instε.elems |>.image (fun x => sizeOf' (next x)) |> insert 0 |> Finset.max' (H := Finset.insert_nonempty ..))
| .readXBus _ next =>
  1 + (instδ.elems |>.image (fun x => sizeOf' (next x)) |> insert 0 |> Finset.max' (H := Finset.insert_nonempty ..))

noncomputable instance instSizeOf' [instδ : Fintype δ] [instε : Fintype ε] : SizeOf (PinStateM ξ ι δ ε α) :=
  ⟨sizeOf'⟩

theorem sizeOf_map {p : PinStateM ξ ι δ ε α} {f : α → β} : sizeOf (f <$> p) = sizeOf p := by
  cases p <;> simp [Functor.map, bind] <;> apply sizeOf_map

theorem sizeOf'_map [Fintype δ] [Fintype ε] {p : PinStateM ξ ι δ ε α} {f : α → β} : sizeOf' (f <$> p) = sizeOf' p := by
  match p with
  | .pure _ => rfl
  | .writeSimpleIO .. | .writeXBus .. =>
    simp [Functor.map, bind, sizeOf']
    apply sizeOf'_map
  | .readSimpleIO _ next | .readXBus _ next =>
    simp [Functor.map, bind, sizeOf']
    congr 3
    funext e
    apply sizeOf'_map

instance [ToString ξ] [ToString ι] [ToString δ] [ToString ε] [ToString α] [Zero δ] [Zero ε]: ToString (PinStateM ξ ι δ ε α) :=
  ⟨go⟩
where
  go
  | .pure a => s!".pure ({toString a})"
  | .readSimpleIO pin next => s!".readSimpleIO {pin} (fun | 0 => {go (next 0)} | ⋯)"
  | .readXBus pin next => s!".readXBus {pin} (fun | 0 => {go (next 0)} | ⋯)"
  | .writeSimpleIO pin d next => s!".writeSimpleIO {pin} {d} ({go next})"
  | .writeXBus pin d next => s!".writeXBus {pin} {d} ({go next})"

end PinStateM
