import JSP000930NegativePolynomialActiveApprox
import JSP000930GenericPinnedNamedPoint

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000933.SetLanguage
  JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem map_halfRadiusBound {C : Type} [NontrivialCompleteBooleanAlgebra C]
    (F : CompleteValueMap B C) (z : ComplexBits B) (K : ℕ) :
    F.toFun (halfRadiusBound z K) = halfRadiusBound (z.map F) K := by
  simp only [halfRadiusBound,map_weightedCut_subset,ComplexBits.map_normSq,mapCut_checked]

private theorem fineTowerError_mono_from {n N : ℕ} (hn : N ≤ n) :
    fineTowerError n ≤ fineTowerError N := by
  unfold fineTowerError
  have hn' : n = N+(n-N) := by omega
  calc
    (1/2 : ℚ)^n = (1/2 : ℚ)^(N+(n-N)) := congrArg (fun k => (1/2 : ℚ)^k) hn'
    _ = (1/2 : ℚ)^N*(1/2 : ℚ)^(n-N) := pow_add _ _ _
    _ ≤ (1/2 : ℚ)^N*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    _ = (1/2 : ℚ)^N := mul_one _

theorem actualFineTower_preserves_pin
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) (j : J) (hj : j ∈ p.pins) (hSite : (site j).CutOn (⊤ : B)) :
    let F := polynomialBaseValueMap site H
    let T := actualFinePolynomialTower site H
    let z := (site j).map F
    let y := (p.eval (site j)).map F
    traceValue (polynomialQ site H) (some p) ≤
      (taylorLimitBits T.limitCoefficients z).name =ᴮ y.name := by
  let Q := polynomialQ site H
  let F := polynomialBaseValueMap site H
  let T := actualFinePolynomialTower site H
  let z := (site j).map F
  let y := (p.eval (site j)).map F
  let m := traceValue Q (some p)
  let w := taylorLimitBits T.limitCoefficients z
  change m ≤ w.name =ᴮ y.name
  have hT : T.On (⊤ : TotalBA Q) := actualFinePolynomialTower_on site H
  have hZ : z.CutOn (⊤ : TotalBA Q) := by
    simpa only [z,F.map_top] using ComplexBits.map_cutOn F hSite
  have hm : m ≤ F.toFun (polyValid site H p) := by
    change traceValue Q (some p) ≤ baseEmbed Q (polyValid site H p)
    apply (supportProjection_le_iff_r428 Q _ _).mp
    rw [traceValue_support_r429]
    exact le_rfl
  have hpY : (p.eval (site j)).CutOn (polyValid site H p) :=
    eval_cutOn_of_coeff (show polyValid site H p ≤ coeffValue p.coeff from inf_le_left)
      (complexCutOn_mono le_top hSite)
  have hY : y.CutOn m := complexCutOn_mono hm (ComplexBits.map_cutOn F hpY)
  have hZm : z.CutOn m := complexCutOn_mono le_top hZ
  have hCover := halfRadiusBound_cover z m hZm
  apply (le_inf le_rfl hCover).trans
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun hK => ?_
  let s := m ⊓ halfRadiusBound z K
  have hsm : s ≤ m := inf_le_left
  have hTs : T.On s := hT.mono le_top
  refine T.limit_eq_of_active_approximation s hTs z y
    (complexCutOn_mono hsm hZm) (complexCutOn_mono hsm hY) ?_
  intro e he
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one he (show (1/2 : ℚ) < 1 by norm_num)
  let R := max K N
  refine ⟨R,fun t ht l => ?_⟩
  let a := l.val
  have htk : K ≤ t := (le_max_left K N).trans ht
  have htn : N ≤ t := (le_max_right K N).trans ht
  have hRad : (K : ℝ)/2 < (a.radius : ℝ) := by
    have hr : K+2 ≤ a.radius := by
      exact (Nat.add_le_add_right htk 2).trans l.property.1
    have hr' : (K : ℝ)+2 ≤ (a.radius : ℝ) := by exact_mod_cast hr
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
    linarith
  have hBudget : a.budget ≤ e := l.property.2.le.trans
    ((fineTowerError_mono_from htn).trans hN.le)
  have hA := activeTrace_pin_bound_at_radius site H a p j hj hSite K hRad
  let d := traceValue Q (some a)
  have hG : s ⊓ d ≤ (d ⊓ m) ⊓ F.toFun (halfRadiusBound (site j) K) := by
    rw [map_halfRadiusBound]
    exact le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have hD : s ⊓ d ≤ distanceLe (((a.eval (site j)).map F)) y a.budget := by
    rw [← map_distanceLe]
    exact hG.trans hA
  have hEq : (a.eval (site j)).map F = mixedPolynomialEval (T.coeff t l) z := by
    rw [PolyTrace.eval_map]
    rfl
  rw [hEq] at hD
  exact hD.trans (distanceLe_mono_nonneg _ _ a.budget_pos.le hBudget)

theorem actualFineTower_pin_literal_eval {n : ℕ}
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) (j : J) (hj : j ∈ p.pins) (hSite : (site j).CutOn (⊤ : B))
    (v : DVec (V (TotalBA (polynomialQ site H))) n) (A Z Y : STerm n)
    (hA : bTerm v A = towerLimitCodeName (actualFinePolynomialTower site H))
    (hZ : bTerm v Z = ((site j).map (polynomialBaseValueMap site H)).name) :
    let F := polynomialBaseValueMap site H
    let m := traceValue (polynomialQ site H) (some p)
    m ≤ bTruth v (evalAt_f A Z Y) ↔ m ≤ bTerm v Y =ᴮ ((p.eval (site j)).map F).name := by
  let F := polynomialBaseValueMap site H
  let T := actualFinePolynomialTower site H
  let m := traceValue (polynomialQ site H) (some p)
  let z := (site j).map F
  have hZ' : z.CutOn m := by
    apply complexCutOn_mono (show m ≤ (⊤ : TotalBA (polynomialQ site H)) from le_top)
    simpa only [z,F.map_top] using ComplexBits.map_cutOn F hSite
  have hT := (actualFinePolynomialTower_on site H).mono
    (show m ≤ (⊤ : TotalBA (polynomialQ site H)) from le_top)
  have he := actualFineTower_preserves_pin site H p j hj hSite
  exact (towerLimitCode_eval_iff v A Z Y T z m hA hZ hT hZ').trans
    ⟨fun h => bSet.bv_trans h he,fun h => bSet.bv_trans h (he.trans_eq bSet.bv_eq_symm)⟩

end JSP000930.Negative
