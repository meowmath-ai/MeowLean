import JSP000930PositiveCommonFiniteCutApproximation

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem strict_rational_gap_of_oriented_cut_bit
    {β γ : RatPresentation → B} {m : B} {q : RatPresentation}
    (hβ : ProperCutOn m β) (hm : m ≠ ⊥)
    (hq : m ≤ β q) (hγq : m ≤ (γ q)ᶜ) :
    ∃ (r : RatPresentation) (d : B),d ≠ ⊥ ∧ d ≤ m ∧
      q.value < r.value ∧ d ≤ β r ∧ d ≤ (γ q)ᶜ := by
  have hc : m ≤ ⨆ r,⨆ (_ : q.value < r.value), β r :=
    (le_inf le_rfl hq).trans (hβ.2.2.2 q)
  obtain ⟨r,c,hcNZ,hcm,hcr⟩ := exists_nonzero_below_choice_r135 m hm
    (fun r => ⨆ (_ : q.value < r.value), β r) hc
  have hr : q.value < r.value := by
    by_contra hnot
    exact hcNZ (le_bot_iff.mp (hcr.trans (iSup_le fun h => (hnot h).elim)))
  exact ⟨r,c,hcNZ,hcm,hr,hcr.trans (iSup_le fun _ => le_rfl),hcm.trans hγq⟩

theorem fixed_rational_cut_bounds_pass_to_completion
    {β : RatPresentation → B} {m : B} (hβ : ProperCutOn m β)
    (p : ℕ → B) (hp : ∀ n,p n ≤ m) (hNZ : ∀ n,p n ≠ ⊥)
    (box : ∀ n : ℕ,narrowRationalPair n) (z : ℝ)
    (he : ∀ n,RationalEncloses β (box n).val.1 (box n).val.2 (p n) ∧
        ((box n).val.1.value : ℝ) ≤ z ∧ z ≤ ((box n).val.2.value : ℝ))
    (q : RatPresentation) :
    (m ≤ β q → (q.value : ℝ) ≤ z) ∧ (m ≤ (β q)ᶜ → z ≤ (q.value : ℝ)) := by
  have hwidth (n : ℕ) : ((box n).val.2.value : ℝ)-((box n).val.1.value : ℝ) <
      (1/2 : ℝ)^n := by
    let scale : ℚ := (1/2 : ℚ)^n
    have h : ((((box n).val.2.value - (box n).val.1.value) : ℚ) : ℝ) < (scale : ℝ) :=
      Rat.cast_lt.mpr (box n).property.2
    dsimp only [scale] at h
    push_cast at h
    exact h
  constructor
  · intro hq
    by_contra! hn
    obtain ⟨n,hclose⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hn)
      (show (1/2 : ℝ) < 1 by norm_num)
    obtain ⟨heₙ,hlo,hup⟩ := he n
    have hQ := enclosure_positive_width hβ (hp n) (hNZ n)
      ⟨(hp n).trans hq,heₙ.2⟩
    have hRc : (q.value : ℝ) < ((box n).val.2.value : ℝ) := by exact_mod_cast hQ
    linarith only [hRc,hlo,hwidth n,hclose]
  · intro hq
    by_contra! hn
    obtain ⟨n,hclose⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hn)
      (show (1/2 : ℝ) < 1 by norm_num)
    obtain ⟨heₙ,hlo,hup⟩ := he n
    have hQ := enclosure_positive_width hβ (hp n) (hNZ n)
      ⟨heₙ.1,(hp n).trans hq⟩
    have hRc : ((box n).val.1.value : ℝ) < (q.value : ℝ) := by exact_mod_cast hQ
    linarith only [hRc,hup,hwidth n,hclose]

end JSP000930.Positive
