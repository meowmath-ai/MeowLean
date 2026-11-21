import JSP000930NegativeFinitePolynomialLiteral
import JSP000930PolynomialTraceValues
import Mathlib.Analysis.Complex.Liouville

open Fol Lattice Set Filter
open scoped Flypitch bSet BigOperators Topology

namespace JSP000930.Negative

open JSP000930.Analytic

theorem radiusCode_eventuallyZero (a : ℕ → ℂ) {N : ℕ}
    (h : ∀ n ≥ N,a n = 0) : RadiusCode a := by
  intro R hR
  let T := ∑ n ∈ Finset.range N, ‖a n‖*(R : ℝ)^n
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
  obtain ⟨b,hb⟩ := exists_nat_gt T
  refine ⟨b,fun n => ?_⟩
  by_cases hn : n < N
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr hn
    exact (Finset.single_le_sum (f := fun k => ‖a k‖*(R : ℝ)^k)
      (fun k _ => by positivity) hm).trans hb.le
  · rw [h n (le_of_not_gt hn)]
    simp

theorem eval_of_eventuallyZero (a : ℕ → ℂ) {N : ℕ}
    (h : ∀ n ≥ N,a n = 0) (z : ℂ) :
    evaluate a z = partialSum a z N := by
  have ha := radiusCode_eventuallyZero a h
  have hA := (hasSum_evaluate ha z).tendsto_sum_nat
  change Tendsto (partialSum a z) atTop (𝓝 (evaluate a z)) at hA
  have he : (partialSum a z) =ᶠ[atTop] (fun _ : ℕ => partialSum a z N) := by
    refine eventually_atTop.2 ⟨N,fun n hn => ?_⟩
    unfold partialSum
    exact Finset.eventually_constant_sum (fun i hi => by simp [h i hi]) hn
  have hC : Tendsto (partialSum a z) atTop (𝓝 (partialSum a z N)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => partialSum a z N) atTop
      (𝓝 (partialSum a z N))).congr' he.symm
  exact tendsto_nhds_unique hA hC

theorem evalSub_of_radius {a b : ℕ → ℂ} (ha : RadiusCode a)
    (hb : RadiusCode b) (hc : RadiusCode (fun n => a n-b n)) (z : ℂ) :
    evaluate (fun n => a n-b n) z = evaluate a z - evaluate b z := by
  have h := (hasSum_evaluate ha z).sub (hasSum_evaluate hb z)
  exact (hasSum_evaluate hc z).unique (by simpa [sub_mul] using h)

theorem taylor_evaluate_of_radius {a : ℕ → ℂ} (ha : RadiusCode a) :
    taylor (evaluate a) = a := by
  have hf := differentiable_evaluate ha
  exact evaluate_injective (radiusCode_taylor hf) ha (evaluate_taylor hf)

theorem coeffDifference_sphereEstimate {a b : ℕ → ℂ} (ha : RadiusCode a)
    (hb : RadiusCode b) (hc : RadiusCode (fun n => a n-b n))
    {R D : ℝ} (hR : 0 < R)
    (h : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖evaluate a z-evaluate b z‖ ≤ D)
    (n : ℕ) : ‖a n-b n‖ * R^n ≤ D := by
  let c : ℕ → ℂ := fun i => a i-b i
  let f : ℂ → ℂ := evaluate c
  have hf : Differentiable ℂ f := differentiable_evaluate hc
  have hT : taylor f = c := taylor_evaluate_of_radius hc
  have hS : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D := by
    intro z hz
    change ‖evaluate c z‖ ≤ D
    simpa only [c,evalSub_of_radius ha hb hc z] using h z hz
  have hD := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (c := (0 : ℂ)) hf.diffContOnCl hS
  have hR' : 0 < R^n := pow_pos hR _
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn0 : (n.factorial : ℝ) ≠ 0 := ne_of_gt hn
  have he := congrFun hT n
  change taylor f n = a n-b n at he
  rw [← he]
  simp only [taylor,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖ * R^n =
        (‖iteratedDeriv n f 0‖ * R^n)/(n.factorial : ℝ) := by rw [div_eq_mul_inv]; ring
    _ ≤ D := by
      apply (div_le_iff₀ hn).mpr
      simpa [mul_comm] using (le_div_iff₀ hR').mp hD

theorem norm_bound_from_grid {F : ℂ → ℂ} (hF : Continuous F) (R : ℕ) {e : ℝ}
    (h : ∀ g : RatGrid R, ‖F (gridPoint g)‖ ≤ e) {z : ℂ}
    (hz : ‖z‖ < (R : ℝ)) : ‖F z‖ ≤ e := by
  let U : Set ℂ := Set.range (gridPoint (R := R))
  have hmem : z ∈ closure U := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ := min (ε/2) (((R : ℝ)-‖z‖)/2)
    have hδ : 0 < δ := lt_min (by positivity) (by linarith)
    obtain ⟨p,q,hpq⟩ := exists_rational_center z δ hδ
    let w := discCenter (p,q,0)
    have hdist : dist z w < δ := hpq
    have hw : ‖w‖ < (R : ℝ) := by
      have hx : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w-z) z
      have h₂ : ‖w-z‖ < δ := by
        rw [← dist_eq_norm,dist_comm]
        exact hdist
      have hδR := min_le_right (ε/2) (((R : ℝ)-‖z‖)/2)
      linarith
    have hgw : p^2+q^2 ≤ (R : ℚ)^2 := by
      have hsq : ‖w‖^2 ≤ (R : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hw.le 2
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hsq
      change (p : ℝ)*(p : ℝ)+(q : ℝ)*(q : ℝ) ≤ (R : ℝ)^2 at hsq
      exact_mod_cast (by simpa [pow_two] using hsq :
        (p : ℝ)^2+(q : ℝ)^2 ≤ (R : ℝ)^2)
    let g : RatGrid R := ⟨(p,q),hgw⟩
    refine ⟨w,⟨g,rfl⟩,?_⟩
    exact hdist.trans ((min_le_left _ _).trans_lt (by linarith))
  let C : Set ℂ := {x | ‖F x‖ ≤ e}
  have hC : IsClosed C := isClosed_le hF.norm continuous_const
  have hs : U ⊆ C := by rintro _ ⟨g,rfl⟩; exact h g
  exact closure_minimal hs hC hmem

end JSP000930.Negative
