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

deriving instance Repr for ByteArray

structure Mem where
  bytes : ByteArray
  hsize : bytes.size = Mem.size := by decide
  hzero : ∀ (i : Index), i > .max → (bytes.get i.toNat (hsize ▸ i.toNat_lt_size)) = 0
    := by decide
deriving Repr

namespace Mem

/-- All zeroes -/
def default : Mem where
  bytes := ⟨Array.replicate size 0⟩
  hsize := by simp [ByteArray.size]
  hzero := by simp [ByteArray.get]

instance : Inhabited Mem := ⟨default⟩

end Mem

inductive ProgramIO.Terminal (α : Type u)
| pure : α → ProgramIO.Terminal α
| writeOut (d : Data) (a : α)
| halted

inductive ProgramIO (α : Type u)
| terminal : ProgramIO.Terminal α → ProgramIO α
/-- Waiting on a value from input. -/
| readIn (next : Data → ProgramIO α)

namespace ProgramIO

def pure (a : α) :=
  terminal (.pure a)

def writeOut (d : Data) (a : α) :=
  terminal (.writeOut d a)

def halted : ProgramIO α :=
  terminal .halted

def writeIfNotAlreadyWritten (toWrite : Data) : ProgramIO α → ProgramIO α
| .pure a => .writeOut toWrite a
| .readIn next => .readIn fun toRead =>
  writeIfNotAlreadyWritten toWrite (next toRead)
| .writeOut d a => .writeOut d a -- ignore write in this case
| .halted => .halted

def bind : ProgramIO α → (α → ProgramIO β) → ProgramIO β
| .pure a, f => f a
| .readIn next, f => .readIn fun d => bind (next d) f
| .writeOut d a, f => writeIfNotAlreadyWritten d (f a) -- don't overwrite the write-out of `f a`, if it exists
| .halted, _ => .halted

instance : Monad ProgramIO where
  pure := pure
  bind := bind

end ProgramIO

structure State where
  mem : Mem
  idx : Index
deriving Inhabited, Repr

namespace Mem

theorem index_valid {idx : Index} : idx.toNat < size :=
  idx.toNat_lt_size

theorem index_valid' {idx : Index} {mem : Mem} : idx.toNat < mem.bytes.size :=
  mem.hsize ▸ index_valid

def getByte (mem : Mem) (idx : Index) : Data :=
  (mem.bytes.get idx.toNat index_valid').toInt8

def read (mem : Mem) (idx : Index) : ProgramIO Data :=
  match idx with
  | .in => .readIn pure
  | .out => pure 0
  | .halt => .halted
  | _ => pure (mem.getByte idx)

def setByte (mem : Mem) (i : Index) (val : Data) (h : i ≤ .max := by decide) : Mem where
  bytes := mem.bytes.set i.toNat val.toUInt8 index_valid'
  hsize := by
    simp [ByteArray.set, ByteArray.size]
    exact mem.hsize
  hzero := by
    intro j hj
    have := mem.hzero j hj
    simp [ByteArray.set, ByteArray.get] at ⊢ this
    rw [←this]
    apply Array.getElem_set_ne
    apply Nat.ne_of_lt
    rw [←UInt8.lt_iff_toNat_lt]
    exact UInt8.lt_of_le_of_lt h hj

def write (mem : Mem) (idx : Index) (val : Data) : ProgramIO Mem :=
  if h₁ : idx = .in then pure mem
  else if h₂ : idx = .out then .writeOut val mem
  else if h₃ : idx = .halt then .halted
  else pure (setByte mem idx val (by simp at *; grind))

end Mem

def State.step (state : State) : ProgramIO State := do
  let ⟨mem, instrAddress⟩ := state
  let a : Index := Int8.toUInt8 (mem.getByte instrAddress)
  let b : Index := Int8.toUInt8 (mem.getByte (instrAddress + 1))
  let c : Index := Int8.toUInt8 (mem.getByte (instrAddress + 2))
  let (memA, memB) ← (match a, b with
    | .in, .in => do
      /- erratum #4: reading from `@IN` multiple times
      only consumes a single input -/
      let input ← mem.read .in
      pure (input, input)
    | _, _ => do pure (←mem.read a, ←mem.read b))

  let mem' ← mem.write a (memA - memB)
  let instrAddress' := if memA ≤ memB then c else (instrAddress + 3)

  return { mem := mem', idx := instrAddress' }

def State.eval (inputs : List Data) (init : ProgramIO State) (maxIters : Nat := 1024) : List Data :=
  (go inputs [] maxIters init).reverse
where go inputs (acc : List Data) fuel (io : ProgramIO State) :=
  match fuel with
  | 0 => acc
  | k + 1 =>
    match io with
    | .halted => acc
    | .pure state =>
      go inputs acc k (step state)
    | .readIn next =>
      match inputs with
      | [] => acc
      | hd :: tl =>
        go tl acc k (next hd)
    | .writeOut d state =>
      go inputs (d :: acc) k (step state)

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

def Mem.ofString (s : String) := do
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

#eval do
  let prog ← Mem.ofString "00	fd	03	00	fd	06	fe	00	09	00	00	00	00	00	00	00"
  let initialState := State.mk prog 0
  let inputs := [1, 1, 1, 2, 1, -1, 11, 25, 82, 17]
  let result := State.eval inputs (pure initialState)
  return result
