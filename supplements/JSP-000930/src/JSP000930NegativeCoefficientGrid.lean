import JSP000930NegativePolynomialCauchyEstimate

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem trace_zeroPadded_coeff_after {p : ℕ → B} (hp : Antitone p)
    (hn : ∀ n,p n ≠ ⊥) {m : B} (hpm : ∀ n,p n ≤ m)
    (f : List (ComplexBits B)) (a : ℕ → ℂ)
    (hA : ∀ n,ComplexDecisionTrace p (zeroPaddedPoly f n) (a n))
    (i : ℕ) (hi : f.length ≤ i) : a i = 0 := by
  have he : zeroPaddedPoly f i = ComplexBits.ofNat 0 :=
    padCoeff_eq_zero_after (ComplexBits.ofNat 0) f i hi
  have h := hA i
  rw [he] at h
  have h0 : ComplexDecisionTrace p (ComplexBits.ofNat 0) (0 : ℂ) := by
    simpa using ComplexDecisionTrace.ofNat p 0
  exact trace_complex_eq hp hn hpm h h0 (le_top.trans bSet.bv_refl)

theorem trace_named_horner_eval {p : ℕ → B} (hp : Antitone p)
    (hn : ∀ n,p n ≠ ⊥) {m : B} (hpm : ∀ n,p n ≤ m)
    (f : List (ComplexBits B)) (a : ℕ → ℂ) (z : ComplexBits B) (x : ℂ)
    (hf : ∀ c ∈ f,c.CutOn m) (hA : ∀ n,ComplexDecisionTrace p (zeroPaddedPoly f n) (a n))
    (hz : z.CutOn m) (hZ : ComplexDecisionTrace p z x) :
    ComplexDecisionTrace p (mixedPolynomialEval f z) (evaluate a x) := by
  rw [eval_of_eventuallyZero a (trace_zeroPadded_coeff_after hp hn hpm f a hA) x]
  exact trace_mixedPolynomialEval_zeroPadded hp hpm f a z x hf hA hz hZ

theorem coefficient_distance_from_grid (f g : List (ComplexBits B)) (m : B)
    (hf : ∀ c ∈ f,c.CutOn m) (hg : ∀ c ∈ g,c.CutOn m)
    (R : ℕ) (hR : 0 < R) (e : ℚ) (he : 0 ≤ e)
    (hGrid : ∀ q : RatGrid (R+1),m ≤ distanceLe
      (mixedPolynomialEval f (ComplexBits.checked (gridPoint q)))
      (mixedPolynomialEval g (ComplexBits.checked (gridPoint q))) e)
    (k : ℕ) :
    m ≤ distanceLe (zeroPaddedPoly f k) (zeroPaddedPoly g k) (e/(R : ℚ)^k) := by
  let u (j : Bool × ℕ) : ComplexBits B :=
    if j.1 then zeroPaddedPoly g j.2 else zeroPaddedPoly f j.2
  have hU (j : Bool × ℕ) : (u j).CutOn m := by
    rcases j with ⟨j,b⟩
    cases j
    · exact zeroPaddedPoly_cutOn f m hf b
    · exact zeroPaddedPoly_cutOn g m hg b
  refine distanceLe_of_finite_metric_law u m hU (false,k) (true,k) _ ?_
  intro p w hp hn hpm ht
  let a (j : ℕ) := w (false,j)
  let b (j : ℕ) := w (true,j)
  have hA (j : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly f j) (a j) := ht (false,j)
  have hB (j : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly g j) (b j) := ht (true,j)
  have hA0 := trace_zeroPadded_coeff_after hp hn hpm f a hA
  have hB0 := trace_zeroPadded_coeff_after hp hn hpm g b hB
  have ha := radiusCode_eventuallyZero a hA0
  have hb := radiusCode_eventuallyZero b hB0
  have hc := radiusCode_eventuallyZero (fun j => a j-b j) (N := max f.length g.length)
    (fun j hj => by rw [hA0 j ((le_max_left _ _).trans hj),hB0 j ((le_max_right _ _).trans hj),sub_zero])
  have hRr : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hCont : Continuous (fun z => evaluate a z-evaluate b z) :=
    (differentiable_evaluate ha).continuous.sub (differentiable_evaluate hb).continuous
  have hGrid' (q : RatGrid (R+1)) : ‖evaluate a (gridPoint q)-evaluate b (gridPoint q)‖ ≤ (e : ℝ) := by
    let z := ComplexBits.checked (B := B) (gridPoint q)
    have hz : z.CutOn m := ComplexBits.checked_cutOn _ _
    have hZ : ComplexDecisionTrace p z (gridPoint q) := checked_complex_traces p _
    have tF := trace_named_horner_eval hp hn hpm f a z (gridPoint q) hf hA hz hZ
    have tG := trace_named_horner_eval hp hn hpm g b z (gridPoint q) hg hB hz hZ
    have hD := trace_distanceLe hp hn hpm (mixedPolynomialEval_cutOn f z hf hz)
      (mixedPolynomialEval_cutOn g z hg hz) tF tG he (hGrid q)
    simpa only [dist_eq_norm] using hD
  have hSphere : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖evaluate a z-evaluate b z‖ ≤ (e : ℝ) := by
    intro z hz
    have hnZ : ‖z‖ = (R : ℝ) := by simpa [Metric.mem_sphere,dist_zero_right] using hz
    have ht : ‖z‖ < ((R+1 : ℕ) : ℝ) := by rw [hnZ]; exact_mod_cast Nat.lt_succ_self R
    exact norm_bound_from_grid hCont (R+1) hGrid' ht
  have hC := coeffDifference_sphereEstimate ha hb hc hRr hSphere k
  have hD : dist (a k) (b k) ≤ (e : ℝ)/(R : ℝ)^k := by
    rw [dist_eq_norm]
    exact (le_div_iff₀ (pow_pos hRr k)).2 hC
  have hS := pow_le_pow_left₀ dist_nonneg hD 2
  simpa [a,b] using hS

end JSP000930.Negative
