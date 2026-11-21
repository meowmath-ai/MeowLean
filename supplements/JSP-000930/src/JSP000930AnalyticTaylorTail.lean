import JSP000930AnalyticTaylor
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped BigOperators Topology

namespace JSP000930.Analytic

theorem term_bound_half_radius {a : ℕ → ℂ} {R B n : ℕ} {z : ℂ}
    (ha : ∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (B : ℝ)) (hz : ‖z‖ ≤ (R : ℝ)/2) :
    ‖a n * z^n‖ ≤ (B : ℝ) * (1/2 : ℝ)^n := by
  have he : (R : ℝ)/2 = (R : ℝ) * (1/2 : ℝ) := by ring
  calc
    ‖a n * z^n‖ = ‖a n‖ * ‖z‖^n := by rw [norm_mul, norm_pow]
    _ ≤ ‖a n‖ * ((R : ℝ)/2)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg (a n))
    _ = (‖a n‖ * (R : ℝ)^n) * (1/2 : ℝ)^n := by rw [he, mul_pow, mul_assoc]
    _ ≤ (B : ℝ) * (1/2 : ℝ)^n :=
      mul_le_mul_of_nonneg_right (ha n) (by positivity)

theorem tail_eq {a : ℕ → ℂ} (ha : RadiusCode a) (z : ℂ) (N : ℕ) :
    evaluate a z - partialSum a z N = ∑' n : ℕ, a (n+N) * z^(n+N) := by
  let f : ℕ → ℂ := fun n => a n * z^n
  have hs : Summable f := (hasSum_evaluate ha z).summable
  have hf : (∑ i ∈ Finset.range N, f i) + (∑' i : ℕ, f (i+N)) = ∑' i : ℕ, f i :=
    hs.sum_add_tsum_nat_add N
  change ((∑' i : ℕ, f i) - (∑ i ∈ Finset.range N, f i)) = ∑' i : ℕ, f (i+N)
  rw [← hf]
  abel

noncomputable def tailBudget (B N : ℕ) : ℝ := 2 * (B : ℝ) * (1/2 : ℝ)^N

theorem evaluate_sub_partialSum_le {a : ℕ → ℂ} (ha : RadiusCode a)
    {R B : ℕ} {z : ℂ} (hB : ∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (B : ℝ))
    (hz : ‖z‖ ≤ (R : ℝ)/2) (N : ℕ) :
    ‖evaluate a z - partialSum a z N‖ ≤ tailBudget B N := by
  rw [tail_eq ha z N]
  have hgeom : HasSum (fun n : ℕ => (1/2 : ℝ)^n) 2 := by
    have h := hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hbound : HasSum (fun n : ℕ => (B : ℝ) * (1/2 : ℝ)^(n+N)) (tailBudget B N) := by
    convert hgeom.mul_left ((B : ℝ) * (1/2 : ℝ)^N) using 1
    · funext n
      rw [pow_add]
      ring
    · unfold tailBudget
      ring
  exact tsum_of_norm_bounded hbound (fun n => term_bound_half_radius hB hz)

theorem evaluate_ne_of_partialSum_separation {a b : ℕ → ℂ} (ha : RadiusCode a)
    (hb : RadiusCode b) {R A B N : ℕ} {z : ℂ}
    (hA : ∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (A : ℝ))
    (hB : ∀ j : ℕ, ‖b j‖ * (R : ℝ)^j ≤ (B : ℝ))
    (hz : ‖z‖ ≤ (R : ℝ)/2)
    (hsep : tailBudget A N + tailBudget B N < ‖partialSum a z N - partialSum b z N‖) :
    evaluate a z ≠ evaluate b z := by
  intro h
  have he : partialSum a z N - partialSum b z N =
    (partialSum a z N - evaluate a z) + (evaluate b z - partialSum b z N) := by
    rw [h]
    abel
  have h1 : ‖partialSum a z N - evaluate a z‖ ≤ tailBudget A N := by
    rw [norm_sub_rev]
    exact evaluate_sub_partialSum_le ha hA hz N
  have h2 := evaluate_sub_partialSum_le hb hB hz N
  have h3 := norm_add_le (partialSum a z N - evaluate a z) (evaluate b z - partialSum b z N)
  rw [← he] at h3
  linarith

theorem tendsto_tailBudget_zero (B : ℕ) :
    Tendsto (tailBudget B) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
  have hz : Tendsto (fun n : ℕ => 2 * (B : ℝ) * (1 / 2 : ℝ)^n)
      atTop (𝓝 ((2 * (B : ℝ)) * 0)) := h.const_mul (2 * (B : ℝ))
  rw [mul_zero] at hz
  exact hz

theorem eventually_partialSum_separation {a b : ℕ → ℂ} (ha : RadiusCode a)
    (hb : RadiusCode b) {R A B : ℕ} {z : ℂ}
    (hA : ∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (A : ℝ))
    (hB : ∀ j : ℕ, ‖b j‖ * (R : ℝ)^j ≤ (B : ℝ))
    (hz : ‖z‖ ≤ (R : ℝ)/2) (hneq : evaluate a z ≠ evaluate b z) :
    ∀ᶠ N : ℕ in atTop,
      tailBudget A N + tailBudget B N < ‖partialSum a z N - partialSum b z N‖ := by
  let δ : ℝ := ‖evaluate a z - evaluate b z‖
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  have ht : Tendsto (fun N => tailBudget A N + tailBudget B N) atTop (𝓝 0) := by
    simpa only [zero_add] using (tendsto_tailBudget_zero A).add (tendsto_tailBudget_zero B)
  have hsmall : ∀ᶠ N : ℕ in atTop, tailBudget A N + tailBudget B N < δ/2 :=
    ht.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsmall] with N hN
  have h1 := evaluate_sub_partialSum_le ha hA hz N
  have h2 : ‖partialSum b z N - evaluate b z‖ ≤ tailBudget B N := by
    rw [norm_sub_rev]
    exact evaluate_sub_partialSum_le hb hB hz N
  have h3 := norm_add_le (partialSum a z N - partialSum b z N)
    (partialSum b z N - evaluate b z)
  have h4 := norm_add_le (evaluate a z - partialSum a z N)
    ((partialSum a z N - partialSum b z N) + (partialSum b z N - evaluate b z))
  have he : evaluate a z - partialSum a z N +
      ((partialSum a z N - partialSum b z N) + (partialSum b z N - evaluate b z)) =
        evaluate a z - evaluate b z := by abel
  rw [he] at h4
  change δ ≤ _ at h4
  linarith

end JSP000930.Analytic
