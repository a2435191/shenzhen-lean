import Mathlib.Tactic.Lemma

namespace Int16

lemma eq_minValue_iff_dvd_toInt {a : Int16} : (a = .minValue ∨ a = 0) ↔ 2^15 ∣ a.toInt := by
  constructor
  · rintro (h|h) <;> (rw [h]; decide)
  · intro ⟨k, hk⟩
    have hk_lt : k < 1 := by
      apply Int.lt_of_mul_lt_mul_left (a := 2^15) ?_ (by decide)
      rw [show (2^15: Int) * 1 = 32767 + 1 by decide]
      apply Int.lt_add_one_of_le
      rw [←hk]
      apply toInt_le
    have hk_ge : k ≥ -1 := by
      refine Int.not_lt.mp fun hn => ?_
      refine absurd (le_toInt a) (Int.not_le_of_gt ?_)
      rw [hk]
      exact Int.mul_lt_mul_of_pos_left hn (by decide)

    match k with
    | -1 =>
      left
      rwa [show (2^15: Int) * (-1) = (-2^15: Int16).toInt by decide,
           toInt_inj
      ] at hk
    | 0 =>
      right
      rwa [show (2^15: Int) * 0 = (0: Int16).toInt by decide,
           toInt_inj
      ] at hk

lemma toInt_neg' {a : Int16} (ha : a ≠ .minValue) : (-a).toInt = -(a.toInt) := by
  rw [toInt_neg, Int.neg_bmod]
  simp only [Nat.reducePow, Int.cast_ofNat_Int, toInt_bmod]
  simp only [show (65536: Int) = 2 * 2^15 by decide,
            @Int.mul_dvd_mul_iff_left 2 _ _ (by decide)]
  simp only [←eq_minValue_iff_dvd_toInt, ha, false_or]
  split <;> simp_all

lemma mod_lt_of_pos (a : Int16) {b : Int16} (hb : b > 0) : a % b < b := by
  rw [lt_iff_toInt_lt, toInt_mod]
  apply Int.tmod_lt_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

lemma lt_mod_of_pos (a : Int16) {b : Int16} (hb : b > 0) : -b < a % b := by
  rw [lt_iff_toInt_lt,
      @toInt_neg' b (by intro; simp_all),
      toInt_mod]
  apply Int.lt_tmod_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

lemma neg_le_neg_iff {a b : Int16} (ha : a ≠ .minValue) (hb : b ≠ .minValue) : -a ≤ -b ↔ b ≤ a := by
  rw [le_iff_toInt_le, le_iff_toInt_le]
  rw [toInt_neg' ha, toInt_neg' hb]
  simp only [Int.neg_le_neg_iff]

end Int16

namespace Int

lemma negSucc_eq'' {n : Nat} : -[n+1] = -n.succ :=
  rfl

private lemma bmod_ofNat_le {k n : Nat} : Int.bmod k n ≤ k := by
  rw [bmod, ofNat_mod_ofNat]
  split
  case' isFalse =>
    apply Int.le_trans (Int.sub_le_self _ (natCast_nonneg n))
  all_goals
    rw [ofNat_le]
    apply Nat.mod_le

lemma bmod_le_natAbs {k : Int} {n : Nat} : k.bmod n ≤ k.natAbs := by
  match hk : k with
  | .ofNat i => simp [bmod_ofNat_le]
  | -[i+1] =>
    rw [negSucc_eq'', neg_bmod, natAbs_neg, natAbs_natCast]
    split
    · exact bmod_ofNat_le
    · simp only [bmod]
      split
      · rw [←natCast_emod]
        apply neg_natCast_le_natCast
      · rw [Int.neg_sub]
        apply Int.sub_left_le_of_le_add
        rename_i h
        norm_cast at ⊢ h
        generalize i.succ = j at *
        calc n
          _ ≤ (n + 1) / 2 + (n + 1) / 2 := by omega
          _ ≤ j % n + j % n := by omega
          _ ≤ j % n + j := Nat.add_le_add_left (Nat.mod_le ..) _

lemma natAbs_le_iff {x : Int} {y : Nat} : x.natAbs ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  omega

end Int
