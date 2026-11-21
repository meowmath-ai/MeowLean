import JSP000930NegativePolynomialValueDistance

open Fol Lattice Filter
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem grid_distanceLe_at_named_point (f g : List (ComplexBits B))
    (z : ComplexBits B) (m : B) (hf : ∀ c ∈ f,c.CutOn m) (hg : ∀ c ∈ g,c.CutOn m)
    (hz : z.CutOn m) (K R : ℕ) (hK : m ≤ halfRadiusBound z K)
    (hR : (K : ℝ)/2 < (R : ℝ)) (e : ℚ) (he : 0 ≤ e)
    (hGrid : ∀ q : RatGrid R,m ≤ distanceLe
        (mixedPolynomialEval f (ComplexBits.checked (gridPoint q)))
        (mixedPolynomialEval g (ComplexBits.checked (gridPoint q))) e) :
    m ≤ distanceLe (mixedPolynomialEval f z) (mixedPolynomialEval g z) e := by
  let x := mixedPolynomialEval f z
  let y := mixedPolynomialEval g z
  let u := distanceCut x y
  let v := checkedRealBits (B := B) ((e : ℝ)^2)
  let X : Option (Bool × ℕ) → ComplexBits B := fun i => match i with
    | none => z
    | some (false,n) => zeroPaddedPoly f n
    | some (true,n) => zeroPaddedPoly g n
  have hX (i : Option (Bool × ℕ)) : (X i).CutOn m := by
    rcases i with _ | ⟨b,n⟩
    · exact hz
    · cases b
      · exact zeroPaddedPoly_cutOn f m hf n
      · exact zeroPaddedPoly_cutOn g m hg n
  have hx : x.CutOn m := mixedPolynomialEval_cutOn f z hf hz
  have hy : y.CutOn m := mixedPolynomialEval_cutOn g z hg hz
  change m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v
  refine cutSubset_of_decision_law X m hX u v (proper_distanceCut hx hy) ?_
  intro p w hp hn hpm hTr
  let a (n : ℕ) := w (some (false,n))
  let b (n : ℕ) := w (some (true,n))
  let point := w none
  have ta (n : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly f n) (a n) := hTr (some (false,n))
  have tb (n : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly g n) (b n) := hTr (some (true,n))
  have tZ : ComplexDecisionTrace p z point := hTr none
  have ta0 := trace_zeroPadded_coeff_after hp hn hpm f a ta
  have tb0 := trace_zeroPadded_coeff_after hp hn hpm g b tb
  have hA := radiusCode_eventuallyZero a ta0
  have hB := radiusCode_eventuallyZero b tb0
  have hCont : Continuous (fun z => evaluate a z-evaluate b z) :=
    (differentiable_evaluate hA).continuous.sub (differentiable_evaluate hB).continuous
  have hG (q : RatGrid R) : ‖evaluate a (gridPoint q)-evaluate b (gridPoint q)‖ ≤ (e : ℝ) := by
    let z0 := ComplexBits.checked (B := B) (gridPoint q)
    have hz0 : z0.CutOn m := ComplexBits.checked_cutOn _ _
    have tZ0 : ComplexDecisionTrace p z0 (gridPoint q) := checked_complex_traces p _
    have hA0 := trace_named_horner_eval hp hn hpm f a z0 (gridPoint q) hf ta hz0 tZ0
    have hB0 := trace_named_horner_eval hp hn hpm g b z0 (gridPoint q) hg tb hz0 tZ0
    have hd := trace_distanceLe hp hn hpm (mixedPolynomialEval_cutOn f z0 hf hz0)
      (mixedPolynomialEval_cutOn g z0 hg hz0) hA0 hB0 he (hGrid q)
    simpa only [dist_eq_norm] using hd
  have hzR : ‖point‖ < (R : ℝ) := (trace_halfRadius_bound hp hn hpm hz tZ hK).trans_lt hR
  have hBound := norm_bound_from_grid hCont R hG hzR
  have tA := trace_named_horner_eval hp hn hpm f a z point hf ta hz tZ
  have tB := trace_named_horner_eval hp hn hpm g b z point hg tb hz tZ
  have hD : dist (evaluate a point) (evaluate b point) ≤ (e : ℝ) := by
    simpa only [dist_eq_norm] using hBound
  exact ⟨(dist (evaluate a point) (evaluate b point))^2,(e : ℝ)^2,
    trace_distanceCut hp hpm hx hy tA tB,checkedRealBits_traces p _,
    pow_le_pow_left₀ dist_nonneg hD 2⟩

end JSP000930.Negative
