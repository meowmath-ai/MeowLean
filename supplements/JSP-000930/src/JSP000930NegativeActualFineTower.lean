import JSP000930NegativePolynomialTower
import JSP000930GenericFineTraceCovers

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing
  JSP000933.BooleanCompletion

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def polynomialBaseValueMap (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) : CompleteValueMap B (TotalBA (polynomialQ site H)) where
  toFun := baseEmbed (polynomialQ site H)
  injective := fun _ _ h => le_antisymm
    ((baseEmbed_reflects_r428 _).mp h.le) ((baseEmbed_reflects_r428 _).mp h.ge)
  monotone := baseEmbed_mono_r427 _
  map_bot := baseEmbed_bot_r427 _
  map_top := baseEmbed_top_r427 _
  map_compl := baseEmbed_compl_r427 _
  map_inf := baseEmbed_meets_r429 _
  map_iSup := baseEmbed_joins_r427 _
  map_iInf := by
    intro I u
    let Q := polynomialQ site H
    have h : (⨅ i,u i) = (⨆ i,(u i)ᶜ)ᶜ := by rw [compl_iSup]; simp only [compl_compl]
    rw [h,baseEmbed_compl_r427,baseEmbed_joins_r427]
    simp only [baseEmbed_compl_r427,compl_iSup,compl_compl]

noncomputable def fineTowerError (n : ℕ) : ℚ := (1/2)^n

theorem fineTowerError_pos (n : ℕ) : 0 < fineTowerError n := by unfold fineTowerError; positivity

noncomputable def actualFinePolynomialTower (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) : NamedPolynomialTower (TotalBA (polynomialQ site H)) where
  Label := fun n => FineTrace B J (n+2) (fineTowerError n)
  active := fun _ l => traceValue (polynomialQ site H) (some l.val)
  coeff := fun _ l => l.val.coeff.map (ComplexBits.map (polynomialBaseValueMap site H))

theorem distanceLe_mono_nonneg {C : Type} [NontrivialCompleteBooleanAlgebra C]
    (x y : ComplexBits C) {e e' : ℚ} (he : 0 ≤ e) (hh : e ≤ e') :
    distanceLe x y e ≤ distanceLe x y e' := by
  have hh' : (e : ℝ) ≤ (e' : ℝ) := by exact_mod_cast hh
  have hk : (e : ℝ)^2 ≤ (e' : ℝ)^2 :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (e : ℝ) by exact_mod_cast he) hh' 2
  simp only [distanceLe,weightedRationalSet_subset]
  refine iInf_mono fun q => ?_
  unfold imp
  apply sup_le_sup_left
  by_cases h : (q.value : ℝ) < (e : ℝ)^2
  · simp [checkedRealBits,JSP000933.PositiveForcing.crispTruth,h,h.trans_le hk]
  · simp [checkedRealBits,JSP000933.PositiveForcing.crispTruth,h]

theorem actualFinePolynomialTower_on (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) :
    (actualFinePolynomialTower site H).On ⊤ := by
  let Q := polynomialQ site H
  let F := polynomialBaseValueMap site H
  constructor
  · intro n
    exact (finePolynomialTrace_cover site H (n+2) (fineTowerError n) (fineTowerError_pos n)).ge
  · intro n l c hc
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    have hA : traceValue Q (some l.val) ≤ baseEmbed Q (polyValid site H l.val) := by
      apply (supportProjection_le_iff_r428 Q _ _).mp
      rw [traceValue_support_r429]
      exact le_rfl
    have hCut : d.CutOn (polyValid site H l.val) :=
      (le_coeffValue_iff _ _).mp (show polyValid site H l.val ≤ coeffValue l.val.coeff from inf_le_left) d hd
    exact JSP000930.AnalyticSyntax.complexCutOn_mono (inf_le_right.trans hA)
      (ComplexBits.map_cutOn F hCut)
  · intro R hR e he
    obtain ⟨M,hM⟩ := exists_pow_lt_of_lt_one (show 0 < e/2 by positivity)
      (show (1/2 : ℚ) < 1 by norm_num)
    let N := max M R
    refine ⟨N,fun i j hi hj l r g => ?_⟩
    have hiM : M ≤ i := (le_max_left _ _).trans hi
    have hjM : M ≤ j := (le_max_left _ _).trans hj
    have hiR : R ≤ l.val.radius := by
      have hh : R ≤ i := (le_max_right M R).trans hi
      exact hh.trans ((Nat.le_add_right i 2).trans l.property.1)
    have hjR : R ≤ r.val.radius := by
      have hh : R ≤ j := (le_max_right M R).trans hj
      exact hh.trans ((Nat.le_add_right j 2).trans r.property.1)
    have hPow (n : ℕ) (hn : M ≤ n) : fineTowerError n ≤ (1/2 : ℚ)^M := by
      unfold fineTowerError
      have hsplit : n = M + (n-M) := by omega
      calc
        (1/2 : ℚ)^n = (1/2 : ℚ)^(M+(n-M)) := congrArg (fun k => (1/2 : ℚ)^k) hsplit
        _ = (1/2 : ℚ)^M*(1/2 : ℚ)^(n-M) := pow_add _ _ _
        _ ≤ (1/2 : ℚ)^M*1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
        _ = (1/2 : ℚ)^M := mul_one _
    have hBud : l.val.budget+r.val.budget ≤ e := by
      have h₁ := l.property.2.trans_le (hPow i hiM)
      have h₂ := r.property.2.trans_le (hPow j hjM)
      linarith
    let z := ComplexBits.checked (B := B) (gridPoint g)
    let ll := l.val.eval z
    let rr := r.val.eval z
    have active := activeTrace_disc_bound site H l.val r.val R hiR hjR g
    have hu : traceValue Q (some l.val) ⊓ traceValue Q (some r.val) ≤
        distanceLe (ll.map F) (rr.map F) (l.val.budget+r.val.budget) := by
      rw [← map_distanceLe]
      exact active
    have hm1 : ll.map F = mixedPolynomialEval
        (l.val.coeff.map (ComplexBits.map F)) (ComplexBits.checked (gridPoint g)) := by
      dsimp only [ll,rr,PolyTrace.eval]
      rw [map_mixedPolynomialEval,ComplexBits.map_checked]
    have hm2 : rr.map F = mixedPolynomialEval
        (r.val.coeff.map (ComplexBits.map F)) (ComplexBits.checked (gridPoint g)) := by
      dsimp only [ll,rr,PolyTrace.eval]
      rw [map_mixedPolynomialEval,ComplexBits.map_checked]
    have hpos : 0 ≤ l.val.budget+r.val.budget :=
      add_nonneg l.val.budget_pos.le r.val.budget_pos.le
    exact inf_le_right.trans ((hu.trans (distanceLe_mono_nonneg _ _ hpos hBud)).trans_eq
      (by rw [hm1,hm2]; rfl))

end JSP000930.Negative
