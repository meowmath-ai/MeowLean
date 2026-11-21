import JSP000930NegativePolynomialTowerEndpoint

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedPolynomialTower.stage_distance_of_active_choices
    (T : NamedPolynomialTower B) (m : B) (h : T.On m)
    (t : ℕ) (z w : ComplexBits B) (hz : z.CutOn m) (hw : w.CutOn m)
    (e : ℚ) (he : 0 ≤ e)
    (hChoices : ∀ l : T.Label t,m ⊓ T.active t l ≤
      distanceLe (mixedPolynomialEval (T.coeff t l) z) w e) :
    m ≤ distanceLe (taylorLimitBits (T.coefficient t) z) w e := by
  let u := taylorLimitBits (T.coefficient t) z
  let c := firstChoiceCell (T.active t)
  have hU : u.CutOn m := taylorLimitBits_cutOn _ _ _ (T.coefficient_proper m h t) hz (T.stageGrowth m h t)
  have hC : m ≤ ⨆ l,c l := by simpa only [c,iSup_firstChoiceCell] using h.cover t
  apply (le_inf le_rfl hC).trans
  rw [inf_iSup_eq]
  refine iSup_le fun l => ?_
  let p := m ⊓ c l
  let q := mixedPolynomialEval (T.coeff t l) z
  have hpm : p ≤ m := inf_le_left
  have hp : p ≤ c l := inf_le_right
  have hpa : p ≤ m ⊓ T.active t l :=
    le_inf hpm (hp.trans (firstChoiceCell_le_active _ _))
  have hz' := complexCutOn_mono hpm hz
  have hw' := complexCutOn_mono hpm hw
  have hq : q.CutOn p := mixedPolynomialEval_cutOn _ z
    (fun x hx => complexCutOn_mono hpa (h.proper t l x hx)) hz'
  have heq := T.stage_eval_eq_horner_on_cell m h t l z p hpm hp hz'
  exact distanceLe_congr_of_named_eq (complexCutOn_mono hpm hU) hw' hq hw' he heq
    (le_top.trans bSet.bv_refl) (hpa.trans (hChoices l))

theorem NamedPolynomialTower.limit_eq_of_active_approximation
    (T : NamedPolynomialTower B) (m : B) (h : T.On m)
    (z w : ComplexBits B) (hz : z.CutOn m) (hw : w.CutOn m)
    (hApprox : ∀ e : ℚ,0 < e → ∃ N : ℕ,∀ t ≥ N,∀ l : T.Label t,
      m ⊓ T.active t l ≤ distanceLe (mixedPolynomialEval (T.coeff t l) z) w e) :
    m ≤ (taylorLimitBits T.limitCoefficients z).name =ᴮ w.name := by
  apply T.limit_eq_of_stage_approximation m h z w hz hw
  intro e he
  obtain ⟨N,hN⟩ := hApprox e he
  exact ⟨N,fun t ht => T.stage_distance_of_active_choices m h t z w hz hw e he.le (hN t ht)⟩

end JSP000930.Negative
