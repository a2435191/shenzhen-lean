import Shenzhen.Clamp

structure Integer where
  n : Int16
  le : n ≤ 999 := by decide
  ge : -999 ≤ n := by decide
deriving DecidableEq, BEq

instance : Repr Integer :=
  ⟨(reprPrec ·.n)⟩

instance : ReprAtom Integer :=
  ⟨⟩

instance : Inhabited Integer :=
  ⟨{ n := 0 }⟩

instance : Coe Integer Int16 :=
  ⟨(·.n)⟩

def Integer.ofInt (n : Int) (h₁ : n ≤ 999) (h₂ : -999 ≤ n) :=
  have : Int16.ofInt n ≤ Int16.ofInt 999 ∧ Int16.ofInt (-999) ≤ Int16.ofInt n := by
    constructor <;> (
      apply (Int16.ofInt_le_iff_le ..).mpr
      all_goals first | trivial | grind only)
  Integer.mk (Int16.ofInt n) this.left this.right

instance instOfNatInteger : OfNat Integer n where
  ofNat :=
    let n' := n.toInt16
    if h : -999 ≤ n' ∧ n' ≤ 999 then
      ⟨n', h.right, h.left⟩
    else panic! "In `instOfNatInteger`: argument is not in [-999, 999]!"

/-- Lift a binary operation on `Int16`s to `Integer`s by clamping the result
to `[-999, 999]`. -/
@[inline]
private def Integer.liftOp (f : Int16 → Int16 → Int16) : Integer → Integer → Integer
| ⟨a, _, _⟩, ⟨b, _, _⟩ => ⟨
  clamp (f a b) (-999) 999,
  clamp_le_hi (by decide), lo_le_clamp (by decide)⟩

instance : Add Integer := ⟨Integer.liftOp Int16.add⟩
instance : Sub Integer := ⟨Integer.liftOp Int16.sub⟩
instance : Mul Integer := ⟨Integer.liftOp Int16.mul⟩

/-- The `not` operation. -/
instance : Complement Integer where
  complement
  | ⟨0, _, _⟩ => 100
  | _ => 0

theorem Int16.eq_minValue_iff_dvd_toInt {a : Int16} : (a = .minValue ∨ a = 0) ↔ 2^15 ∣ a.toInt := by
  constructor
  · rintro (h|h) <;> (rw [h]; decide)
  · intro ⟨k, hk⟩
    have hk_lt : k < 1 := by
      apply Int.lt_of_mul_lt_mul_left (a := 2^15) ?_ (by decide)
      rw [show (2^15: Int) * 1 = 32767 + 1 by decide]
      apply Int.lt_add_one_of_le
      rw [←hk]
      apply Int16.toInt_le _
    have hk_ge : k ≥ -1 := by
      refine Int.not_lt.mp fun hn => ?_
      refine absurd (Int16.le_toInt a) (Int.not_le_of_gt ?_)
      rw [hk]
      exact Int.mul_lt_mul_of_pos_left hn (by decide)

    match k with
    | -1 =>
      left
      rwa [show (2^15: Int) * (-1) = (-2^15: Int16).toInt by decide,
           Int16.toInt_inj
      ] at hk
    | 0 =>
      right
      rwa [show (2^15: Int) * 0 = (0: Int16).toInt by decide,
           Int16.toInt_inj
      ] at hk

theorem Int16.toInt_neg' {a : Int16} (ha : a ≠ .minValue) : (-a).toInt = -(a.toInt) := by
  rw [Int16.toInt_neg, Int.neg_bmod]
  simp only [Nat.reducePow, Int.cast_ofNat_Int, toInt_bmod]
  simp only [show (65536: Int) = 2 * 2^15 by decide,
            @Int.mul_dvd_mul_iff_left 2 _ _ (by decide)]
  simp only [←Int16.eq_minValue_iff_dvd_toInt, ha, false_or]
  split <;> simp_all

theorem Int16.mod_lt_of_pos (a : Int16) {b : Int16} (hb : b > 0) : a % b < b := by
  rw [lt_iff_toInt_lt, toInt_mod]
  apply Int.tmod_lt_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

theorem Int16.lt_mod_of_pos (a : Int16) {b : Int16} (hb : b > 0) : -b < a % b := by
  rw [lt_iff_toInt_lt,
      @Int16.toInt_neg' b (by intro; simp_all),
      toInt_mod]
  apply Int.lt_tmod_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

theorem Int16.neg_le_neg_iff {a b : Int16} (ha : a ≠ .minValue) (hb : b ≠ .minValue) : -a ≤ -b ↔ b ≤ a := by
  rw [Int16.le_iff_toInt_le, Int16.le_iff_toInt_le]
  rw [Int16.toInt_neg' ha, Int16.toInt_neg' hb]
  simp

/-- `dgt` stands for "digit get." It preserves sign. -/
def Integer.dgt (acc target : Integer) : Integer :=
  have h₁ {n : Int16} : n % 10 ≤ 999 :=
    Int16.le_of_lt (Int16.lt_of_lt_of_le (Int16.mod_lt_of_pos n (by decide)) (by decide))
  have h₂ {n : Int16} : -999 ≤ n % 10 :=
    Int16.le_of_lt (Int16.lt_of_le_of_lt (by decide) (Int16.lt_mod_of_pos n (by decide)))

  match target with
  | ⟨0, _, _⟩ => ⟨acc.n % 10, h₁, h₂⟩
  | ⟨1, _, _⟩ => ⟨(acc.n / 10) % 10, h₁, h₂⟩
  | ⟨2, _, _⟩ => ⟨(acc.n / 100) % 10, h₁, h₂⟩ -- TODO: remove unnecessary % 10 call. Requires work to show bounds
  | _ => 0

/-- `dst` stands for "digit set" -/
def Integer.dst (acc target new : Integer) : Integer :=
  -- In case `new` is outside [-9, 9]
  let newDigit := new.n % 10 -- with the same sign as `new`
  panic! "`dst` is unimplemented!" -- TODO

-- Just for entering literals
instance : Neg Integer where
  neg
  | ⟨n, le, ge⟩ =>
    have : n ≠ Int16.minValue := by
      intro hn
      rw [hn] at ge
      contradiction
    {
      n := -n,
      le := show -n ≤ - -999 from
        (Int16.neg_le_neg_iff this (by decide)).mpr ge,
      ge :=
        (Int16.neg_le_neg_iff (by decide) this).mpr le
    }

instance : LT Integer :=
  ⟨(·.n < ·.n)⟩

instance : DecidableLT Integer :=
  fun ⟨a, _, _⟩ ⟨b, _, _⟩ =>
    if h : a < b then .isTrue h
    else .isFalse h
