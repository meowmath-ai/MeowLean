import JSP000930NegativePolynomialLimitDistance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem radiusBudget_add_distance {a b : ComplexBits B} {m : B}
    (ha : a.CutOn m) (hb : b.CutOn m) (R K k L : ℕ) (hR : 0 < R)
    (e : ℚ) (he : 0 ≤ e) (hL : e ≤ (L : ℚ))
    (hD : m ≤ distanceLe a b (e/(R : ℚ)^k)) (hK : m ≤ radiusBudgetBits b R K k) :
    m ≤ radiusBudgetBits a R (K+L) k := by
  let Z : Bool → ComplexBits B := fun i => if i then b else a
  let s := ((R : ℝ)^k)^2
  let u := mulCutBits a.normSq (checkedRealBits s)
  let v := checkedRealBits (B := B) (((K+L : ℕ) : ℝ)^2)
  have hZ (i : Bool) : (Z i).CutOn m := by cases i; exact ha; exact hb
  have hU := mulCutBits_properCut a.normSq (checkedRealBits s) m (ComplexBits.normSq_cutOn ha)
    (properCutOn_mono le_top (checkedRealBits_properCut s))
  change m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v
  refine cutSubset_of_decision_law Z m hZ u v hU ?_
  intro p w hp hn hpm ht
  let x := w false
  let y := w true
  have hx : ComplexDecisionTrace p a x := ht false
  have hy : ComplexDecisionTrace p b y := ht true
  have hT := (hx.normSq hp hpm ha).mul hp hpm (checkedRealBits_traces p s)
    (ComplexBits.normSq_cutOn ha) (properCutOn_mono le_top (checkedRealBits_properCut s))
  have hD' := trace_distanceLe hp hn hpm ha hb hx hy (by positivity) hD
  have hb' := trace_budget_to_norm (trace_radiusBudget_at hp hn hpm hy hb ((hpm 0).trans hK))
  have hR' : 0 < (R : ℝ) := by exact_mod_cast hR
  have hDreal : ‖x-y‖ * (R : ℝ)^k ≤ (e : ℝ) := by
    apply (le_div_iff₀ (pow_pos hR' k)).mp
    simpa only [dist_eq_norm,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast] using hD'
  have htriangle : ‖x‖ ≤ ‖x-y‖+‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  have hL' : (e : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hFinal : ‖x‖ * (R : ℝ)^k ≤ ((K+L : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right htriangle (show 0 ≤ (R : ℝ)^k by positivity)
    push_cast
    rw [add_mul] at hh
    linarith
  refine ⟨Complex.normSq x*s,((K+L : ℕ) : ℝ)^2,hT,checkedRealBits_traces p _,?_⟩
  change Complex.normSq x * (((R : ℝ)^k)^2) ≤ _
  rw [Complex.normSq_eq_norm_sq,← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hFinal 2

theorem radiusBudget_congr_of_eq {a b : ComplexBits B} {m : B}
    (ha : a.CutOn m) (hb : b.CutOn m) (R K k : ℕ) (hR : 0 < R)
    (he : m ≤ a.name =ᴮ b.name) (h : m ≤ radiusBudgetBits b R K k) :
    m ≤ radiusBudgetBits a R K k := by
  have hd := distanceLe_congr_of_named_eq ha hb hb hb (show (0 : ℚ) ≤ 0 from le_rfl)
    he (le_top.trans bSet.bv_refl) (distanceLe_self hb 0)
  have hd' : m ≤ distanceLe a b (0/(R : ℚ)^k) := by simpa using hd
  simpa only [Nat.add_zero] using radiusBudget_add_distance ha hb R K k 0 hR 0
    le_rfl (by simp) hd' h

theorem NamedPolynomialTower.stageGrowth (T : NamedPolynomialTower B) (m : B)
    (h : T.On m) (t : ℕ) : GrowthOn m (T.coefficient t) := by
  intro R hR
  let d := firstChoiceCell (T.active t)
  have hD : m ≤ ⨆ l,d l := by simpa only [d,iSup_firstChoiceCell] using h.cover t
  apply (le_inf le_rfl hD).trans
  rw [inf_iSup_eq]
  refine iSup_le fun l => ?_
  let s := m ⊓ d l
  let f := T.coeff t l
  have hsm : s ≤ m := inf_le_left
  have hsI : s ≤ d l := inf_le_right
  have hsA : s ≤ m ⊓ T.active t l :=
    le_inf hsm (hsI.trans (firstChoiceCell_le_active _ _))
  have hf : ∀ c ∈ f,c.CutOn s := fun c hc =>
    JSP000930.AnalyticSyntax.complexCutOn_mono hsA (h.proper t l c hc)
  have hg := zeroPaddedPoly_growth f s hf R hR
  apply (le_inf le_rfl hg).trans
  rw [inf_iSup_eq]
  refine iSup_le fun K => le_iSup_of_le K (le_iInf fun k => ?_)
  let q := s ⊓ (⨅ n : ℕ,radiusBudgetBits (zeroPaddedPoly f n) R K n)
  have hqs : q ≤ s := inf_le_left
  exact radiusBudget_congr_of_eq
    (JSP000930.AnalyticSyntax.complexCutOn_mono (hqs.trans hsm) (T.coefficient_proper m h t k))
    (JSP000930.AnalyticSyntax.complexCutOn_mono hqs (zeroPaddedPoly_cutOn f s hf k))
    R K k (by omega)
    ((hqs.trans hsI).trans (JSP000930.Positive.sameMaskedComplex_name
      (chosenPolyCoeff_on_cell (T.active t) (T.coeff t) k l)))
    (inf_le_right.trans (iInf_le _ k))

theorem NamedPolynomialTower.limitGrowth (T : NamedPolynomialTower B) (m : B)
    (h : T.On m) : GrowthOn m T.limitCoefficients := by
  intro R hR
  obtain ⟨N,hN⟩ := T.limitCoeff_distance m h R (by omega) 1 zero_lt_one
  have hg := T.stageGrowth m h N R hR
  apply (le_inf le_rfl hg).trans
  rw [inf_iSup_eq]
  refine iSup_le fun K => le_iSup_of_le (K+1) (le_iInf fun k => ?_)
  let q := m ⊓ (⨅ n : ℕ,radiusBudgetBits (T.coefficient N n) R K n)
  have hqm : q ≤ m := inf_le_left
  exact radiusBudget_add_distance
    (JSP000930.AnalyticSyntax.complexCutOn_mono hqm (T.limit_coeff_proper m h k))
    (JSP000930.AnalyticSyntax.complexCutOn_mono hqm (T.coefficient_proper m h N k))
    R K k 1 (by omega) 1 zero_le_one (by simp)
    (hqm.trans (hN N le_rfl k)) (inf_le_right.trans (iInf_le _ k))

end JSP000930.Negative
