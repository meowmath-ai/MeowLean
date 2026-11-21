import JSP000930AnalyticPrefixCauchy

open Lattice Filter
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Analytic JSP000933.BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem cut_le_checked_of_upper {m : B} {u : RatPresentation → B}
    (hu : ProperCutOn m u) (q : RatPresentation) (c : ℝ)
    (hq : (q.value : ℝ) ≤ c) (hb : m ≤ (u q)ᶜ) :
    m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet (checkedRealBits c) := by
  rw [weightedRationalSet_subset]
  refine le_iInf fun r => ?_
  rw [← deduction]
  by_cases hr : (r.value : ℝ) < c
  · simp [checkedRealBits,JSP000933.PositiveForcing.crispTruth,hr]
  · have hqr' : (q.value : ℝ) ≤ (r.value : ℝ) := hq.trans (le_of_not_gt hr)
    have hqr : q.value ≤ r.value := by exact_mod_cast hqr'
    have hfalse : m ⊓ u r ≤ ⊥ := (le_inf
      (hu.2.2.1 q r hqr) (inf_le_left.trans hb)).trans (by simp)
    simp only [checkedRealBits,JSP000933.PositiveForcing.crispTruth,hr,ite_false]
    exact hfalse

theorem halfRadiusBound_cover (Z : ComplexBits B) (m : B) (hZ : Z.CutOn m) :
    m ≤ ⨆ R : ℕ, ⨆ (_ : 1 ≤ R), halfRadiusBound Z R := by
  have hN := ComplexBits.normSq_cutOn hZ
  apply (le_inf le_rfl hN.2.1).trans
  rw [inf_iSup_eq]
  refine iSup_le fun q => ?_
  let d : ℝ := |(q.value : ℝ)|+1
  obtain ⟨R,hR⟩ := exists_nat_gt (2*d)
  have hd : 1 ≤ d := by dsimp [d]; linarith [abs_nonneg (q.value : ℝ)]
  have hRD : d < (R : ℝ)/2 := by linarith
  have hr : 1 ≤ R := by
    have hh : (1 : ℝ) ≤ (R : ℝ) := by linarith
    exact_mod_cast hh
  have hhq : (q.value : ℝ) ≤ (R : ℝ)/2 :=
    (le_abs_self _).trans (by dsimp [d] at hRD; linarith)
  have hhR : (R : ℝ)/2 ≤ ((R : ℝ)/2)^2 := by
    have he : (1 : ℝ) ≤ (R : ℝ)/2 := le_trans hd hRD.le
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ (R : ℝ)/2 by positivity)
    simpa [pow_two] using hm
  exact le_iSup_of_le R (le_iSup_of_le hr
    (cut_le_checked_of_upper (properCutOn_mono inf_le_left hN) q _ (hhq.trans hhR) inf_le_right))

theorem forced_taylorPrefix_cauchy (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hG : GrowthOn m A)
    (im : Bool) (ε : ℚ) (he : 0 < ε) :
    m ≤ ⨆ N : ℕ, cutCauchyTail (fun n => (taylorPrefixBits A Z n).coord im) ε N := by
  apply (le_inf le_rfl (halfRadiusBound_cover Z m hZ)).trans
  rw [inf_iSup_eq]
  refine iSup_le fun R => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun hR => ?_
  let s := m ⊓ halfRadiusBound Z R
  have hs : s ≤ m := inf_le_left
  have hBound : s ≤ ⨆ K : ℕ, ⨅ n : ℕ, radiusBudgetBits (A n) R K n :=
    hs.trans (hG R hR)
  apply (le_inf le_rfl hBound).trans
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  let t := s ⊓ (⨅ n : ℕ, radiusBudgetBits (A n) R K n)
  have htm : t ≤ m := inf_le_left.trans hs
  have htZ : Z.CutOn t := ⟨properCutOn_mono htm hZ.1, properCutOn_mono htm hZ.2⟩
  have htA (n : ℕ) : (A n).CutOn t :=
    ⟨properCutOn_mono htm (hA n).1,properCutOn_mono htm (hA n).2⟩
  obtain ⟨N,hN⟩ := forced_prefixCauchy_of_budget A Z t htA htZ (hG.mono htm)
    R K (inf_le_left.trans inf_le_right) (fun n => inf_le_right.trans (iInf_le _ n)) im ε he
  exact hN.trans (le_iSup _ N)

noncomputable def taylorLimitBits (A : ℕ → ComplexBits B) (Z : ComplexBits B) : ComplexBits B :=
  ⟨roundedLiminfBits (fun n => (taylorPrefixBits A Z n).re),
    roundedLiminfBits (fun n => (taylorPrefixBits A Z n).im)⟩

private theorem taylorPrefix_coord_proper {A : ℕ → ComplexBits B} {Z : ComplexBits B} {m : B}
    (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (n : ℕ) (im : Bool) :
    ProperCutOn m ((taylorPrefixBits A Z n).coord im) := by
  have h := taylorPrefixBits_cutOn (a := A) hZ (m := n) (fun j _ => hA j) n le_rfl
  cases im
  · exact h.1
  · exact h.2

theorem taylorLimitBits_cutOn (A : ℕ → ComplexBits B) (Z : ComplexBits B) (m : B)
    (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hG : GrowthOn m A) :
    (taylorLimitBits A Z).CutOn m := by
  have hi (im : Bool) :
      ProperCutOn m (roundedLiminfBits (fun n => (taylorPrefixBits A Z n).coord im)) := by
    let u : ℕ → RatPresentation → B := fun n => (taylorPrefixBits A Z n).coord im
    have hP (n : ℕ) := taylorPrefix_coord_proper hA hZ n im
    have hc : m ≤ ⨆ N : ℕ, cutCauchyTail u 1 N :=
      forced_taylorPrefix_cauchy A Z m hA hZ hG im 1 zero_lt_one
    obtain ⟨hl,hh⟩ := cutCauchy_limit_proper_nonempty u m hc
      (fun n => (hP n).1) (fun n => (hP n).2.1)
    refine ⟨hl,hh,?_,?_⟩
    · intro q r hqr
      exact inf_le_right.trans (roundedLiminfBits_downward u hqr)
    · intro q
      exact inf_le_right.trans_eq (roundedLiminfBits_rounded u q)
  exact ⟨hi false,hi true⟩

theorem taylorLimitBits_converges (A : ℕ → ComplexBits B) (Z : ComplexBits B) (m : B)
    (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hG : GrowthOn m A) (im : Bool)
    (ε : ℚ) (he : 0 < ε) :
    m ≤ ⨆ N : ℕ, cutConvergesTail (fun n => (taylorPrefixBits A Z n).coord im)
      ((taylorLimitBits A Z).coord im) ε N := by
  let u : ℕ → RatPresentation → B := fun n => (taylorPrefixBits A Z n).coord im
  have hi : (taylorLimitBits A Z).coord im = roundedLiminfBits u := by cases im <;> rfl
  rw [hi]
  exact cutCauchy_roundedLiminf_converges u m
    (fun e h => forced_taylorPrefix_cauchy A Z m hA hZ hG im e h) ε he

end JSP000930.BooleanAnalysis
