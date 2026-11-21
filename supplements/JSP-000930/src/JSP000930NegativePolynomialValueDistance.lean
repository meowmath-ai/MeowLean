import JSP000930NegativePolynomialLimitGrowth
import JSP000930PositiveCommonNativeEvaluationGroundValues

open Fol Lattice Filter
open scoped Flypitch bSet BigOperators

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem evaluators_uniform_halfRadius {a b : ℕ → ℂ} {z : ℂ} {R : ℕ} {e : ℝ}
    (ha : RadiusCode a) (hb : RadiusCode b)
    (h : ∀ n, ‖a n-b n‖*(R : ℝ)^n ≤ e) (hz : ‖z‖ ≤ (R : ℝ)/2) :
    dist (evaluate a z) (evaluate b z) ≤ 2*e := by
  have hterm (n : ℕ) : ‖(a n-b n)*z^n‖ ≤ e*(1/2 : ℝ)^n := by
    have he : (R : ℝ)/2 = (R : ℝ)*(1/2 : ℝ) := by ring
    calc
      ‖(a n-b n)*z^n‖ = ‖a n-b n‖*‖z‖^n := by rw [norm_mul,norm_pow]
      _ ≤ ‖a n-b n‖*((R : ℝ)/2)^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)
      _ = (‖a n-b n‖*(R : ℝ)^n)*(1/2 : ℝ)^n := by rw [he,mul_pow,mul_assoc]
      _ ≤ e*(1/2 : ℝ)^n := mul_le_mul_of_nonneg_right (h n) (by positivity)
  have hG : HasSum (fun n : ℕ => (1/2 : ℝ)^n) 2 := by
    have ht := hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)
    norm_num at ht ⊢
    exact ht
  have hG' : HasSum (fun n : ℕ => e*(1/2 : ℝ)^n) (2*e) := by
    simpa only [mul_comm e 2] using hG.mul_left e
  have hs : HasSum (fun n => (a n-b n)*z^n) (evaluate a z-evaluate b z) := by
    simpa [sub_mul] using (hasSum_evaluate ha z).sub (hasSum_evaluate hb z)
  rw [dist_eq_norm,← hs.tsum_eq]
  exact tsum_of_norm_bounded hG' hterm

theorem namedTaylor_values_distance_of_coeffs (A D : ℕ → ComplexBits B) (z : ComplexBits B)
    (m : B) (ha : ∀ n,(A n).CutOn m) (hd : ∀ n,(D n).CutOn m)
    (hz : z.CutOn m) (hGA : GrowthOn m A) (hGD : GrowthOn m D)
    (R : ℕ) (hR : 0 < R) (hZ : m ≤ halfRadiusBound z R)
    (e : ℚ) (he : 0 ≤ e)
    (hC : ∀ n,m ≤ distanceLe (A n) (D n) (e/(R : ℚ)^n)) :
    m ≤ distanceLe (taylorLimitBits A z) (taylorLimitBits D z) (2*e) := by
  let l := taylorLimitBits A z
  let r := taylorLimitBits D z
  have hl := taylorLimitBits_cutOn A z m ha hz hGA
  have hr := taylorLimitBits_cutOn D z m hd hz hGD
  by_contra hBad
  obtain ⟨q,t,s,hs,hsm,hqt,hLo,hHi⟩ :=
    nonzero_cut_order_countercell (proper_distanceCut hl hr) hBad
  have hmA (n : ℕ) := JSP000930.AnalyticSyntax.complexCutOn_mono hsm (ha n)
  have hmD (n : ℕ) := JSP000930.AnalyticSyntax.complexCutOn_mono hsm (hd n)
  have hmZ := JSP000930.AnalyticSyntax.complexCutOn_mono hsm hz
  obtain ⟨C⟩ := JSP000930.Positive.commonTaylorGroundValues_exists A D z s hs hmA hmD hmZ
    (hGA.mono hsm) (hGD.mono hsm)
  have hpm (i : ℕ) := (C.under i).trans hsm
  have hz' := trace_halfRadius_bound C.antitone C.nonzero C.under hmZ C.pointTrace (hsm.trans hZ)
  have hR' : 0 < (R : ℝ) := by exact_mod_cast hR
  have hOrd (n : ℕ) : ‖C.left n-C.right n‖*(R : ℝ)^n ≤ (e : ℝ) := by
    have h := trace_distanceLe C.antitone C.nonzero hpm (ha n) (hd n)
      (C.leftTrace n) (C.rightTrace n) (by positivity) (hC n)
    apply (le_div_iff₀ (pow_pos hR' n)).mp
    simpa only [dist_eq_norm,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast] using h
  have hD := evaluators_uniform_halfRadius C.leftRadius C.rightRadius hOrd hz'
  rw [C.leftEval,C.rightEval] at hD
  have hD' : dist C.yLeft C.yRight ≤ ((2*e : ℚ) : ℝ) := by
    simpa only [Rat.cast_mul,Rat.cast_ofNat] using hD
  have hSq := pow_le_pow_left₀ dist_nonneg hD' 2
  have hTr := trace_distanceCut C.antitone hpm hl hr C.leftValTrace C.rightValTrace
  have hu := trace_forcedMember_le C.antitone C.nonzero hTr t ⟨0,(C.under 0).trans hLo⟩
  have hv := trace_forcedAbsent_ge C.antitone C.nonzero
    (checkedRealBits_traces C.p ((((2*e : ℚ) : ℝ))^2)) q ⟨0,(C.under 0).trans hHi⟩
  have hGap : (q.value : ℝ) < (t.value : ℝ) := by exact_mod_cast hqt
  exact (not_le_of_gt ((hv.trans_lt hGap).trans_le hu)) hSq

theorem NamedPolynomialTower.eval_stage_distance (T : NamedPolynomialTower B) (m : B)
    (h : T.On m) (z : ComplexBits B) (hz : z.CutOn m) (R : ℕ) (hR : 0 < R)
    (hZ : m ≤ halfRadiusBound z R) (e : ℚ) (he : 0 < e) :
    ∃ N : ℕ, ∀ t ≥ N, m ≤ distanceLe
      (taylorLimitBits T.limitCoefficients z) (taylorLimitBits (T.coefficient t) z) (2*e) := by
  obtain ⟨N,hN⟩ := T.limitCoeff_distance m h R hR e he
  exact ⟨N,fun t ht => namedTaylor_values_distance_of_coeffs T.limitCoefficients (T.coefficient t) z m
    (T.limit_coeff_proper m h) (T.coefficient_proper m h t) hz (T.limitGrowth m h)
    (T.stageGrowth m h t) R hR hZ e he.le (hN t ht)⟩

end JSP000930.Negative
