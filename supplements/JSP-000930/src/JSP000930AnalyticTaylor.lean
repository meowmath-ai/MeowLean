import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace JSP000930.Analytic

def RadiusCode (a : ℕ → ℂ) : Prop :=
  ∀ R : ℕ, 1 ≤ R → ∃ B : ℕ, ∀ n : ℕ, ‖a n‖ * (R : ℝ)^n ≤ (B : ℝ)

def SquaredRadiusCode (a : ℕ → ℂ) : Prop :=
  ∀ R : ℕ, 1 ≤ R → ∃ B : ℕ, ∀ n : ℕ,
    Complex.normSq (a n) * ((R : ℝ)^n)^2 ≤ (B : ℝ)^2

theorem squaredRadiusCode_iff (a : ℕ → ℂ) : SquaredRadiusCode a ↔ RadiusCode a := by
  have hsq (R n : ℕ) : Complex.normSq (a n) * ((R : ℝ)^n)^2 =
      (‖a n‖ * (R : ℝ)^n)^2 := by
    rw [Complex.normSq_eq_norm_sq, mul_pow]
  constructor
  · intro h R hR
    obtain ⟨B, hB⟩ := h R hR
    refine ⟨B, fun n => ?_⟩
    have hh := hB n
    rw [hsq] at hh
    have hx : 0 ≤ ‖a n‖ * (R : ℝ)^n := by positivity
    have hy : 0 ≤ (B : ℝ) := by positivity
    nlinarith
  · intro h R hR
    obtain ⟨B, hB⟩ := h R hR
    refine ⟨B, fun n => ?_⟩
    rw [hsq]
    have hh := hB n
    have hx : 0 ≤ ‖a n‖ * (R : ℝ)^n := by positivity
    have hy : 0 ≤ (B : ℝ) := by positivity
    nlinarith

abbrev EntireCode := {a : ℕ → ℂ // RadiusCode a}

noncomputable def evaluate (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * z^n

noncomputable def partialSum (a : ℕ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * z^n

def EvalAt (a : ℕ → ℂ) (z w : ℂ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    dist (partialSum a z n) w < 1 / (k : ℝ)

theorem ofScalars_radius_top {a : ℕ → ℂ} (ha : RadiusCode a) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := by
  by_contra h
  obtain ⟨R, hR⟩ := ENNReal.exists_nat_gt h
  let S : ℕ := R + 1
  have hRS : R ≤ S := by dsimp [S]; omega
  obtain ⟨B, hB⟩ := ha S (by dsimp [S]; omega)
  have hS : (S : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    have hk := (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_bound (r := (S : ℝ≥0))
      (B : ℝ) (fun n => by
        simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_natCast] using hB n)
    simpa only [ENNReal.coe_natCast] using hk
  have hCast : (R : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by
    exact_mod_cast hRS
  exact (not_lt_of_ge (hCast.trans hS)) hR

theorem evaluate_eq_series_sum (a : ℕ → ℂ) (z : ℂ) :
    evaluate a z = (FormalMultilinearSeries.ofScalars ℂ a).sum z := by
  simp only [evaluate, FormalMultilinearSeries.sum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

theorem hasSum_evaluate {a : ℕ → ℂ} (ha : RadiusCode a) (z : ℂ) :
    HasSum (fun n => a n * z^n) (evaluate a z) := by
  rw [evaluate_eq_series_sum]
  have hz : z ∈ Metric.eball 0 (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simp [ofScalars_radius_top ha]
  have hs := (FormalMultilinearSeries.ofScalars ℂ a).hasSum hz
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hs

theorem analytic_evaluate {a : ℕ → ℂ} (ha : RadiusCode a) :
    AnalyticOnNhd ℂ (evaluate a) Set.univ := by
  intro z _
  have hz : z ∈ Metric.eball 0 (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simp [ofScalars_radius_top ha]
  have hh := (FormalMultilinearSeries.analyticOnNhd
      (p := FormalMultilinearSeries.ofScalars ℂ a)) z hz
  rw [show evaluate a = (FormalMultilinearSeries.ofScalars ℂ a).sum from
    funext (evaluate_eq_series_sum a)]
  exact hh

theorem differentiable_evaluate {a : ℕ → ℂ} (ha : RadiusCode a) :
    Differentiable ℂ (evaluate a) :=
  fun z => (analytic_evaluate ha z (Set.mem_univ z)).differentiableAt

theorem evalAt_iff_tendsto (a : ℕ → ℂ) (z w : ℂ) :
    EvalAt a z w ↔ Tendsto (partialSum a z) atTop (𝓝 w) := by
  constructor
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro e he
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / e)
    have hk0 : (0 : ℝ) < (k : ℝ) := (one_div_pos.mpr he).trans hk
    obtain ⟨N, hN⟩ := h k (by exact_mod_cast hk0)
    refine ⟨N, fun n hn => (hN n hn).trans ?_⟩
    exact (div_lt_iff₀ hk0).2 (by
      have hh := (div_lt_iff₀ he).1 hk
      simpa [mul_comm] using hh)
  · intro h k hk
    exact Metric.tendsto_atTop.mp h _ (one_div_pos.mpr (by exact_mod_cast hk))

theorem evalAt_iff_eq {a : ℕ → ℂ} (ha : RadiusCode a) (z w : ℂ) :
    EvalAt a z w ↔ w = evaluate a z := by
  rw [evalAt_iff_tendsto]
  have h := (hasSum_evaluate ha z).tendsto_sum_nat
  change Tendsto (partialSum a z) atTop (𝓝 (evaluate a z)) at h
  constructor
  · intro hw
    exact tendsto_nhds_unique hw h
  · rintro rfl
    exact h

theorem existsUnique_evalAt {a : ℕ → ℂ} (ha : RadiusCode a) (z : ℂ) :
    ∃! w, EvalAt a z w :=
  ⟨evaluate a z, (evalAt_iff_eq ha z _).2 rfl,
    fun w hw => (evalAt_iff_eq ha z w).1 hw⟩

noncomputable def taylor (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (↑n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

theorem taylor_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n => taylor f n * z^n) (f z) := by
  simpa [taylor, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    Complex.hasSum_taylorSeries_of_entire hf (0 : ℂ) z

theorem radiusCode_taylor {f : ℂ → ℂ} (hf : Differentiable ℂ f) : RadiusCode (taylor f) := by
  intro R _
  let u (n : ℕ) := taylor f n * (R : ℂ)^n
  have hu : Tendsto u atTop (𝓝 0) :=
    (taylor_hasSum hf (R : ℂ)).summable.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu 1 zero_lt_one
  obtain ⟨B, hB⟩ := exists_nat_gt (1 + ∑ i ∈ Finset.range N, ‖u i‖)
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, ‖u i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg (u i)
  refine ⟨B, fun n => ?_⟩
  have hn_eq : ‖u n‖ = ‖taylor f n‖ * (R : ℝ)^n := by
    simp only [u, norm_mul, norm_pow, Complex.norm_natCast]
  rw [← hn_eq]
  by_cases hn : N ≤ n
  · have hsmall : ‖u n‖ < 1 := by simpa only [dist_zero_right] using hN n hn
    linarith
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hprefix : ‖u n‖ ≤ ∑ i ∈ Finset.range N, ‖u i‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (u j)) hmem
    linarith

theorem evaluate_taylor {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    evaluate (taylor f) = f :=
  funext fun z => (taylor_hasSum hf z).tsum_eq

private theorem hasFPowerSeriesAt_evaluate {a : ℕ → ℂ} (ha : RadiusCode a) :
    HasFPowerSeriesAt (evaluate a) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  have hr : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simp [ofScalars_radius_top ha]
  have he : evaluate a = (FormalMultilinearSeries.ofScalars ℂ a).sum :=
    funext (evaluate_eq_series_sum a)
  rw [he]
  exact ((FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall hr).hasFPowerSeriesAt

theorem evaluate_injective {a b : ℕ → ℂ} (ha : RadiusCode a) (hb : RadiusCode b)
    (h : evaluate a = evaluate b) : a = b := by
  have hA := hasFPowerSeriesAt_evaluate ha
  have hB := hasFPowerSeriesAt_evaluate hb
  rw [← h] at hB
  have hseries := hA.eq_formalMultilinearSeries hB
  funext n
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ =>
    p n (fun _ => (1 : ℂ))) hseries
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, one_pow, mul_one] using hn

noncomputable def entireCodeEquiv :
    EntireCode ≃ {f : ℂ → ℂ // Differentiable ℂ f} where
  toFun a := ⟨evaluate a.1, differentiable_evaluate a.2⟩
  invFun f := ⟨taylor f.1, radiusCode_taylor f.2⟩
  left_inv a := Subtype.ext (evaluate_injective
    (radiusCode_taylor (differentiable_evaluate a.2)) a.2
    (evaluate_taylor (differentiable_evaluate a.2)))
  right_inv f := Subtype.ext (evaluate_taylor f.2)

theorem unequal_evaluation_open {a b : ℕ → ℂ} (ha : RadiusCode a) (hb : RadiusCode b) :
    IsOpen {z : ℂ | evaluate a z ≠ evaluate b z} :=
  (isClosed_eq (differentiable_evaluate ha).continuous
    (differentiable_evaluate hb).continuous).isOpen_compl

theorem unequal_evaluation_dense {a b : ℕ → ℂ} (ha : RadiusCode a) (hb : RadiusCode b)
    (hab : a ≠ b) : Dense {z : ℂ | evaluate a z ≠ evaluate b z} := by
  intro z
  rw [mem_closure_iff_nhds]
  intro U hU
  by_contra h
  apply hab (evaluate_injective ha hb ?_)
  apply (analytic_evaluate ha).eq_of_eventuallyEq (analytic_evaluate hb)
  filter_upwards [hU] with x hx
  by_contra hx'
  exact h ⟨x, hx, hx'⟩

end JSP000930.Analytic
