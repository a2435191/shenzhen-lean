import Shenzhen.Integer

inductive ConditionalFlag | none | pos | neg | once
deriving Repr

structure ConditionalState where
  posEnabled : Bool
  negEnabled : Bool
deriving Repr

inductive Pin (ξ : Type u) (ι : Type v)
| xBus (pin : ξ) | simpleIO (pin : ι)
deriving Repr

namespace Instruction

inductive Reg (ρ : Type v) (ξ : Type w) (ι : Type x)
/-- An internal chip register, like `acc` or `dat`. -/
| internal : ρ → Reg ..
/-- An XBus pin register. -/
| xBus : ξ → Reg ..
/-- A simple I/O pin register. -/
| simpleIO : ι → Reg ..
/-- The `null` pseudo-register. -/
| null
deriving Repr

@[inline] def Reg.pin? : Reg ρ ξ ι → Option (Pin ξ ι)
| .xBus i => some (.xBus i)
| .simpleIO i => some (.simpleIO i)
| .null | .internal _ => none

inductive RegOrInt (ρ : Type v) (ξ : Type w) (ι : Type x)
/-- A reference to a register. -/
| reg : Reg ρ ξ ι → RegOrInt ..
/-- An integer literal. -/
| int : Integer → RegOrInt ..
deriving Repr

namespace RegOrInt

@[inline] def pin? : RegOrInt ρ ξ ι → Option (Pin ξ ι)
| .reg r => r.pin?
| .int _ => none

-- Some convenience constructors so I don't have to type `.reg (.internal .acc)` all the time

@[macro_inline] def internal : ρ → RegOrInt ρ ξ ι :=
  .reg ∘ .internal

@[macro_inline] def xBus : ξ → RegOrInt ρ ξ ι :=
  .reg ∘ .xBus

@[macro_inline] def simpleIO : ι → RegOrInt ρ ξ ι :=
  .reg ∘ .simpleIO

@[macro_inline] def null : RegOrInt ρ ξ ι :=
  .reg .null

end RegOrInt

namespace Notation

/-! Notation to make writing `Instruction` easier. -/

set_option hygiene false
scoped notation "R" => Instruction.Reg ρ ξ ι
scoped notation "R/I" => Instruction.RegOrInt ρ ξ ι

end Instruction.Notation

open Instruction.Notation in
/-- All of the MC-series instructions.
Type parameters:
- `Λ` is for *l*abels
- `ρ` is for (internal chip) *r*egisters
- `ξ` is for *X*bus pins
- `ι` is for *I*O pins. -/
inductive Instruction (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x)
-- Basic instructions
| nop
| mov : R/I → R → Instruction ..
| jmp : Λ → Instruction ..
| slp : R/I → Instruction ..
| slx : ξ → Instruction ..
-- Arithmetic instructions
| add : R/I → Instruction ..
| sub : R/I → Instruction ..
| mul : R/I → Instruction ..
| not
| dgt : R/I → Instruction ..
| dst : R/I → R/I → Instruction ..
-- Test instructions
| teq : R/I → R/I → Instruction ..
| tgt : R/I → R/I → Instruction ..
| tlt : R/I → R/I → Instruction ..
| tcp : R/I → R/I → Instruction ..
-- Undocumented instruction
-- | gen : ι → R/I → R/I → Instruction .. -- TODO: add this back in
deriving Inhabited, Repr

def Instruction.mapΛ (instr : Instruction (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x))
    (f : Λ → Λ') : Instruction Λ' ρ ξ ι :=
  match instr with
  | .jmp l => .jmp (f l)
  | .nop => .nop
  | .mov x y => .mov x y
  | .slp x => .slp x | .slx x => .slx x
  | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .not => .not
  | .dgt x => .dgt x | .dst x y => .dst x y
  | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y

@[specialize] def Instruction.mapΛM {m : Type u → Type v} [Functor m] [Pure m]
    {Λ : Type u} {Λ' : Type u} {ρ : Type u} {ξ : Type u} {ι : Type u}
    (f : Λ → m Λ') (instr : Instruction Λ ρ ξ ι)
    : m (Instruction Λ' ρ ξ ι) :=
  match instr with
  | .jmp l => jmp <$> f l
  | .nop => pure <| nop
  | .mov x y => pure <| mov x y
  | .slp x => pure <| slp x | .slx x => pure <| slx x
  | .add x => pure <| add x | .sub x => pure <| sub x | .mul x => pure <| mul x | .not => pure <| not
  | .dgt x => pure <| dgt x | .dst x y => pure <| dst x y
  | .teq x y => pure <| teq x y | .tgt x y => pure <| tgt x y | .tlt x y => pure <| tlt x y | .tcp x y => pure <| tcp x y
