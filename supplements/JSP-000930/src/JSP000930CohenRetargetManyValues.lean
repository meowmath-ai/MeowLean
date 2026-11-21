import JSP000930CohenManyStrictInteriors

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.MarkedForcing

variable {B I K : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype K]

theorem near_Gaussian_components (c d : ℚ × ℚ) (e : ℚ)
    (h : dist (gaussianRat c) (gaussianRat d) ≤ (e : ℝ)) :
    ∀ j,|centerComponent c j-centerComponent d j| ≤ e := by
  have hNorm : ‖gaussianRat c-gaussianRat d‖ ≤ (e : ℝ) := by
    simpa only [dist_eq_norm] using h
  intro j
  cases j
  · have h := (Complex.abs_re_le_norm (gaussianRat c-gaussianRat d)).trans hNorm
    exact_mod_cast (show (|(c.1 : ℝ)-(d.1 : ℝ)| : ℝ) ≤ (e : ℝ) by
      simpa only [gaussianRat,Complex.sub_re] using h)
  · have h := (Complex.abs_im_le_norm (gaussianRat c-gaussianRat d)).trans hNorm
    exact_mod_cast (show (|(c.2 : ℝ)-(d.2 : ℝ)| : ℝ) ≤ (e : ℝ) by
      simpa only [gaussianRat,Complex.sub_im] using h)

set_option maxHeartbeats 600000 in
theorem cohen_retarget_many_earlier_named_values
    (p : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbP : b ≤ p.mask)
    (route : K × Bool → I) (hRoute : Function.Injective route)
    (s : K × Bool → Interval) (c₀ : K → ℚ × ℚ)
    (x : K → ComplexBits B) (hx : ∀ i,(x i).CutOn b)
    (k e : K → ℚ) (hk : ∀ i,0 ≤ k i) (he : ∀ i,0 < e i)
    (hNear : ∀ i,b ≤ distanceLe (x i) (ComplexBits.checked (gaussianRat (c₀ i))) (k i))
    (hInside : ∀ i j,
      ((s (i,j)).follow (completeRowWord p.trace (route (i,j)))).left <
        centerComponent (c₀ i) j - (k i + e i) ∧
      centerComponent (c₀ i) j + (k i + e i) <
        ((s (i,j)).follow (completeRowWord p.trace (route (i,j)))).right) :
    ∃ q : CohenTotal B (I × ℕ), q ≤ p ∧ q.mask ≤ b ∧
      ∀ i,
        let F := markedCompleteValueMap (valuedCohen B (I × ℕ))
        let z := intervalPointBits B (route (i,false)) (route (i,true)) (s (i,false)) (s (i,true))
        imageCondition q ≤ distanceLe z ((x i).map F) (e i + e i) ∧
        imageCondition q ≤ distanceLe z (ComplexBits.checked (gaussianRat (c₀ i))) (e i+(e i+k i)) := by
  let T (i : K) (m : B) := ∃ c : ℚ × ℚ,m ≤ distanceLe (x i) (ComplexBits.checked (gaussianRat c)) (e i)
  have hMono (i : K) {u v : B} (hu : u ≤ v) : T i v → T i u := by
    rintro ⟨c,hc⟩
    exact ⟨c,hu.trans hc⟩
  obtain ⟨a,ha,haB,hA⟩ := exists_finitely_refined_marks T hMono b hb (by
    intro i m hm hmB
    obtain ⟨n,c,hn,hnM,hC⟩ := exists_gaussianRat_approx (x i) m hm (cutOn_mono930 (hx i) hmB)
      (e i) (he i)
    exact ⟨n,hn,hnM,c,hC⟩)
  choose c hC using hA
  have hxA (i : K) := cutOn_mono930 (hx i) haB
  have hCA (i : K) : a ≤ distanceLe (ComplexBits.checked (gaussianRat (c i))) (x i) (e i) :=
    distanceLe_symm_mono (hxA i) (ComplexBits.checked_cutOn _ _) (he i).le le_rfl (hC i)
  have hAB (i : K) : a ≤ distanceLe (ComplexBits.checked (gaussianRat (c i)))
      (ComplexBits.checked (gaussianRat (c₀ i))) (e i+k i) :=
    distanceLe_triangle (ComplexBits.checked_cutOn _ _) (hxA i) (ComplexBits.checked_cutOn _ _)
      (he i).le (hk i) (hCA i) (haB.trans (hNear i))
  have hIn (i : K) (j : Bool) :
      ((s (i,j)).follow (completeRowWord p.trace (route (i,j)))).left < centerComponent (c i) j ∧
      centerComponent (c i) j < ((s (i,j)).follow (completeRowWord p.trace (route (i,j)))).right := by
    have hN := checked_distanceLe_absolute ha (gaussianRat (c i)) (gaussianRat (c₀ i))
      (e i+k i) (add_nonneg (he i).le (hk i)) (hAB i)
    have hD := abs_le.mp (near_Gaussian_components (c i) (c₀ i) (e i+k i) hN j)
    exact ⟨by linarith [(hInside i j).1,hD.1],by linarith [(hInside i j).2,hD.2]⟩
  obtain ⟨q,hqp,hqA,hW⟩ := cohen_refine_many_strict_interior_points p a ha (haB.trans hbP)
    route hRoute s c e he hIn
  let F := markedCompleteValueMap (valuedCohen B (I × ℕ))
  have hB : imageCondition q ≤ F.toFun a := by
    change imageCondition q ≤ baseEmbed (valuedCohen B (I × ℕ)) a
    exact (baseEmbed_reflects_mask_r427 q a).mpr hqA.le
  refine ⟨q,hqp,hqA.le.trans haB,?_⟩
  intro i
  have hA' := hB.trans (F.monotone (hCA i))
  have hB' := hB.trans (F.monotone (hAB i))
  simp only [map_distanceLe,ComplexBits.map_checked] at hA' hB'
  have hMon := cutOn_mono930 (ComplexBits.map_cutOn F (hxA i)) hB
  have hZ := intervalPointBits_valid (route (i,false)) (route (i,true))
    (s (i,false)) (s (i,true)) (imageCondition q)
  exact ⟨distanceLe_triangle hZ (ComplexBits.checked_cutOn _ _) hMon (he i).le (he i).le
      (hW i) hA',
    distanceLe_triangle hZ (ComplexBits.checked_cutOn _ _) (ComplexBits.checked_cutOn _ _)
      (he i).le (add_nonneg (he i).le (hk i)) (hW i) hB'⟩

end JSP000930.Negative.Cohen
