import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- Bespoke `Fintype` class so we don't have to import mathlib. Uses a `List` instead
of a `Finset`. -/
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a, a ∈ elems

instance : Fintype SimpleIOData where
  elems := (List.finRange 101).map fun ⟨n, h⟩ => .ofNat n (Nat.le_of_lt_succ h)
  complete
  | ⟨n, le⟩ => by
    apply List.mem_map.mpr
    have : n.toNat < 101 := by rwa [
      Nat.lt_succ_iff, show 100 = UInt8.toNat 100 from rfl, ←UInt8.le_iff_toNat_le]
    refine ⟨⟨n.toNat, this⟩, ?_, ?_⟩
    · rw [List.finRange, List.mem_ofFn]
      simp
    · simp [SimpleIOData.ofNat]

def Integer.elems : List Integer :=
  (List.finRange (999 + 999 + 1)).map fun ⟨n, h⟩ =>
    let n' := (n : Int) - 999
    have le := by rwa [
      ←Int.le_add_iff_sub_le,
      show (999 + 999 : Int) = (999 + 999).cast from rfl,
      Int.ofNat_le, Nat.le_iff_lt_add_one]
    have ge := by simp [n', ←Int.add_le_iff_le_sub]
    .ofInt n' le ge

instance : Fintype Integer where
  elems := Integer.elems
  complete
  | ⟨n, le, ge⟩ => by
    apply List.mem_map.mpr
    let n' := (n.toInt + 999).toNat
    have : n' < 999 + 999 + 1 := by
      unfold n'
      rw [Nat.lt_succ_iff, Int.toNat_le, Int.add_le_iff_le_sub]
      show n.toInt ≤ Int16.toInt 999
      rwa [←Int16.le_iff_toInt_le]
    refine ⟨⟨n', this⟩, ?_, ?_⟩
    · rw [List.finRange, List.mem_ofFn]
      simp
    · dsimp only [Integer.ofInt, n']
      congr
      rw [Int.ofNat_toNat, show (0 : Int) = -999 + 999 from rfl, Int.max_add_right, Int.add_sub_cancel]
      have : -999 ≤ n.toInt := show Int16.toInt (-999) ≤ n.toInt from
        Int16.le_iff_toInt_le.mp ge
      rw [Int.max_eq_left this, Int16.ofInt_toInt]
