-- https://jaredkrinke.itch.io/sic-1

namespace SIC1

@[reducible] def Index := UInt8
@[reducible] def Data := Int8

namespace Index

@[match_pattern, simp] def max  : Index := 252

@[match_pattern, simp] def «in» : Index := 253

@[match_pattern, simp] def out  : Index := 254

@[match_pattern, simp] def halt : Index := 255

end Index

abbrev Mem.size := 256
@[simp] abbrev Mem.accessibleSize := 253

deriving instance Repr for ByteArray

structure Mem where
  bytes : ByteArray
  hsize : bytes.size = Mem.accessibleSize := by decide
deriving Repr

namespace Mem

/-- All zeroes -/
def default : Mem where
  bytes := ⟨Array.replicate accessibleSize 0⟩
  hsize := by simp [ByteArray.size]

instance : Inhabited Mem := ⟨default⟩

end Mem

/-- Possibly read from `IN`. -/
inductive ProgramIO.Read? (α : Type u)
/-- Don't read any value from `IN`. -/
| none (a : α)
/-- Wait on a value from `IN`. -/
| readIn (ofData : Data → α)
deriving Inhabited

inductive ProgramIO (α : Type u)
/-- Don't write anything, just possibly read. -/
| noWrite : ProgramIO.Read? α → ProgramIO α
/-- After possibly reading from `IN`, write some `Data` to `OUT` and return some `α`. -/
| writeOut : ProgramIO.Read? (Data × α) → ProgramIO α
/-- Halt the program. -/
| halted
deriving Inhabited

-- inductive ProgramIO (α : Type u)
--
-- | none : ProgramIO.Terminal Unit α → ProgramIO α
-- /-- Wait on a value from `IN` and then perform a terminal action. -/
-- | readIn : ProgramIO.Terminal Data α → ProgramIO α
-- deriving Inhabited

namespace ProgramIO

def pure (a : α) : ProgramIO α :=
  .noWrite (.none a)

namespace Read?

def map (f : α → β) : Read? α → Read? β
| .none a => .none (f a)
| .readIn g => .readIn (f ∘ g)

instance : Functor Read? where
  map := map

end Read?

def map (f : α → β) : ProgramIO α → ProgramIO β
| .noWrite r => .noWrite (f <$> r)
| .writeOut r => .writeOut (Prod.map id f <$> r)
| .halted => .halted

instance : Functor ProgramIO where
  map := map

end ProgramIO

structure State where
  mem : Mem
  idx : Index
deriving Inhabited, Repr

namespace Mem

def getByte (mem : Mem) (idx : Index) : Data :=
  if h : idx.toNat < Mem.accessibleSize then
    (mem.bytes.get idx.toNat (mem.hsize ▸ h)).toInt8
  else 0

theorem le_max_iff {i : Index} : i ≤ .max ↔ i < 253 := by
  rw [Index.max, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt]
  exact Nat.lt_add_one_iff.symm

def setByte (mem : Mem) (i : Index) (val : Data) (h : i ≤ .max := by decide) : Mem where
  bytes := mem.bytes.set i.toNat val.toUInt8 <| by
    rwa [mem.hsize, show accessibleSize = UInt8.toNat 253 by rfl,
        ←UInt8.lt_iff_toNat_lt, ←le_max_iff]
  hsize := by
    rw [ByteArray.size, ByteArray.set, Array.size_set,
        ←ByteArray.size, mem.hsize]

instance : ToString Mem where
  toString | { bytes, .. } => toString bytes

end Mem

def State.step : State → ProgramIO State
| ⟨mem, instrAddress⟩ =>
  let a : Index := Int8.toUInt8 (mem.getByte instrAddress)
  let b : Index := Int8.toUInt8 (mem.getByte (instrAddress + 1))
  let c : Index := Int8.toUInt8 (mem.getByte (instrAddress + 2))

  let memAB : ProgramIO.Read? (Data × Data) :=
    match a, b with
    | .in, .in =>
      /- erratum #4: reading from `@IN` multiple times
        only consumes a single input -/
      .readIn fun x => (x, x)
    | .in, _ =>
      .readIn (·, mem.getByte b)
    | _, .in =>
      .readIn (mem.getByte a, ·)
    | _, _ =>
      .none (mem.getByte a, mem.getByte b)

  let memAB.apply {α : Type} (fn : Data → Index → α) : ProgramIO.Read? α :=
    memAB <&> fun (memA, memB) =>
      let res := memA - memB
      let instrAddress' := if res ≤ 0 then c else instrAddress + 3
      fn res instrAddress'

  -- Write `res := mem[A] - mem[B]` to address `A`
  if h : a ≤ .max then
    .noWrite <| memAB.apply fun res instrAddress' =>
      ⟨mem.setByte a res h, instrAddress'⟩
  else
    match a with
    | .halt => .halted
    | .in =>
      .noWrite <| memAB.apply fun _ instrAddress' =>
        ⟨mem, instrAddress'⟩
    | .out =>
      .writeOut <| memAB.apply fun res instrAddress' =>
        ⟨res, mem, instrAddress'⟩
    | _ => unreachable!

def State.eval (inputs : List Data) (init : State) (maxIters : Nat := 1024) : List Data :=
  (go inputs [] maxIters init).reverse
where go (inputs acc : List Data) fuel (state : State) :=
  match fuel with
  | 0 =>
    acc
  | k + 1 =>
    let io := state.step
    match io with
    | .halted => acc
    | .noWrite (.none state') => go inputs acc k state'
    | .noWrite (.readIn next) =>
      match inputs with
      | [] => acc
      | inp :: inputs' => go inputs' acc k (next inp)
    | .writeOut (.none (d, state')) => go inputs (d :: acc) k state'
    | .writeOut (.readIn next) =>
      match inputs with
      | [] => acc
      | inp :: inputs' =>
        let (d, state') := next inp
        go inputs' (d :: acc) k state'

def Mem.ofList (bytes : List Data) (h : bytes.length ≤ Index.max.toNat + 1 := by decide) : Mem :=
  bytes
    |>.mapFinIdx (fun i b hi => (b, Fin.mk i hi))
    |>.foldl (init := .default) fun mem (d, i) =>
      have : i ≤ Index.max.toNat := Nat.le_of_lt_succ <| calc
        _ < bytes.length := i.is_lt
        _ ≤ Index.max.toNat + 1 := h
      let i := UInt8.ofFin (i.castLT (Nat.lt_of_le_of_lt this (by decide)))
      have : i ≤ Index.max := by
        simp [UInt8.le_iff_toFin_le, i]
        exact this
      mem.setByte i d this

def Mem.ofString? (s : String) : Option Mem := do
  let bytes ← s.splitOn "\t"
    |>.mapM (fun
      | String.mk [c₁, c₂] => do
        let d₁ ← toDigit c₁.toUpper
        let d₂ ← toDigit c₂.toUpper
        (16 * d₁ + d₂).toInt8
      | _ => none)
  if h : bytes.length ≤ Index.max.toNat + 1 then
    return ofList bytes h
  else none
where
  toDigit c : Option Index :=
    if '0' ≤ c && c ≤ '9' then
      some (c.toUInt8 - '0'.toUInt8)
    else if 'A' ≤ c && c ≤ 'F' then
      some (c.toUInt8 - 'A'.toUInt8 + 10)
    else none

def prog :=
  "00	fd	03	00	fd	06	fe	00	09	00	00	00	00	00	00	00"
  |> Mem.ofString?
  |> Option.get!

instance [ToString α] : ToString (ProgramIO.Read? α) where
  toString
  | .none a => s!".none {a}"
  | .readIn f => s!".readIn fun | 37 => {f 37} | _ => …"

instance [ToString α] : ToString (ProgramIO α) where
  toString
  | .halted => ".halted"
  | .writeOut r => s!".writeOut <| {r}"
  | .noWrite r => s!".noWrite <| {r}"

instance : ToString State where
  toString | { mem, idx } => s!"⟨{mem}, {idx}⟩"

#eval do
  let initialState := State.mk prog 0
  let inputs := [1, 1, 1, 2, 1, -1, 11, 25, 82, 17]
  let result := State.eval inputs initialState
  return result
