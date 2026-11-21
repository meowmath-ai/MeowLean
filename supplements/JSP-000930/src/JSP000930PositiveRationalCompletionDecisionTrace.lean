import JSP000930PositiveWeightedComplexImpliesProperCuts

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem completion_decides_strict_rational_tests
    {β : RatPresentation → B} {m : B} (hβ : ProperCutOn m β)
    (p : ℕ → B) (idx : ℕ → ℕ) (hp : ∀ n,p n ≤ m)
    (box : ∀ n : ℕ,narrowRationalPair n) (z : ℝ)
    (he : ∀ n,RationalEncloses β (box n).val.1 (box n).val.2 (p (idx n)) ∧
        ((box n).val.1.value : ℝ) ≤ z ∧ z ≤ ((box n).val.2.value : ℝ)) :
    (∀ q : RatPresentation, (q.value : ℝ) < z → ∃ N, p N ≤ β q) ∧
    (∀ q : RatPresentation, z < (q.value : ℝ) → ∃ N, p N ≤ (β q)ᶜ) := by
  have hw (n : ℕ) : ((box n).val.2.value : ℝ)-((box n).val.1.value : ℝ) <
      (1/2 : ℝ)^n := by
    let scale : ℚ := (1/2 : ℚ)^n
    have h : ((((box n).val.2.value - (box n).val.1.value) : ℚ) : ℝ) < (scale : ℝ) :=
      Rat.cast_lt.mpr (box n).property.2
    dsimp only [scale] at h
    push_cast at h
    exact h
  constructor
  · intro q hq
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hq)
      (show (1/2 : ℝ) < 1 by norm_num)
    obtain ⟨hBox,hlo,hup⟩ := he n
    have hLowR : (q.value : ℝ) ≤ ((box n).val.1.value : ℝ) := by
      linarith only [hn,hw n,hup]
    have hLow : q.value ≤ (box n).val.1.value := by exact_mod_cast hLowR
    exact ⟨idx n,(le_inf (hp _) hBox.1).trans (hβ.2.2.1 _ _ hLow)⟩
  · intro q hq
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hq)
      (show (1/2 : ℝ) < 1 by norm_num)
    obtain ⟨hBox,hlo,hup⟩ := he n
    have hHighR : ((box n).val.2.value : ℝ) ≤ (q.value : ℝ) := by
      linarith only [hn,hw n,hlo]
    have hHigh : (box n).val.2.value ≤ q.value := by exact_mod_cast hHighR
    let k := idx n
    have hDisj : Disjoint (p k) (β q) := by
      apply disjoint_iff_inf_le.mpr
      exact (le_inf ((le_inf inf_le_left inf_le_right).trans
            ((inf_le_inf_right _ (hp k)).trans (hβ.2.2.1 _ _ hHigh)))
          (inf_le_left.trans hBox.2)).trans (le_of_eq inf_compl_eq_bot')
    exact ⟨k,le_compl_iff_disjoint_right.mpr hDisj⟩

end JSP000930.Positive
