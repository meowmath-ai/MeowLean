import JSP000930OldCenteredTraceComparison
import JSP000933MarkedNameTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.MarkedForcing

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checked_distanceLe_absolute {m : B} (hm : m ≠ ⊥) (x y : ℂ) (e : ℚ) (he : 0 ≤ e)
    (h : m ≤ distanceLe (ComplexBits.checked x) (ComplexBits.checked y) e) :
    dist x y ≤ (e : ℝ) := by
  let q : ℕ → B := fun _ => m
  exact trace_distanceLe (show Antitone q from fun _ _ _ => le_rfl) (fun _ => hm)
    (fun _ => le_rfl) (ComplexBits.checked_cutOn x m) (ComplexBits.checked_cutOn y m)
    (checked_complex_traces q x) (checked_complex_traces q y) he h

set_option maxHeartbeats 550000 in
theorem cohen_retarget_earlier_named_value
    (p : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbP : b ≤ p.mask)
    (i j : I) (hij : i ≠ j) (s t : Interval) (c₀ : ℚ × ℚ)
    (x : ComplexBits B) (hx : x.CutOn b) (k e : ℚ) (hk : 0 ≤ k) (he : 0 < e)
    (hNear : b ≤ distanceLe x (ComplexBits.checked (gaussianRat c₀)) k)
    (hLi : (s.follow (completeRowWord p.trace i)).left < c₀.1 - (k+e))
    (hRi : c₀.1 + (k+e) < (s.follow (completeRowWord p.trace i)).right)
    (hLj : (t.follow (completeRowWord p.trace j)).left < c₀.2 - (k+e))
    (hRj : c₀.2 + (k+e) < (t.follow (completeRowWord p.trace j)).right) :
    let F := markedCompleteValueMap (valuedCohen B (I × ℕ))
    ∃ q : CohenTotal B (I × ℕ), q ≤ p ∧
      imageCondition q ≤ distanceLe (intervalPointBits B i j s t) (x.map F) (e+e) ∧
      imageCondition q ≤ distanceLe (intervalPointBits B i j s t)
        (ComplexBits.checked (gaussianRat c₀)) (e+(e+k)) := by
  dsimp only
  let F := markedCompleteValueMap (valuedCohen B (I × ℕ))
  obtain ⟨a,c,ha,haB,hA⟩ := exists_gaussianRat_approx x b hb hx e he
  have hxA := cutOn_mono930 hx haB
  let c₁ := ComplexBits.checked (B := B) (gaussianRat c)
  let c₂ := ComplexBits.checked (B := B) (gaussianRat c₀)
  have h1 := distanceLe_symm_mono hxA (ComplexBits.checked_cutOn (gaussianRat c) a)
    he.le le_rfl hA
  have h2 := distanceLe_triangle (ComplexBits.checked_cutOn (gaussianRat c) a) hxA
    (ComplexBits.checked_cutOn (gaussianRat c₀) a) he.le hk h1 (haB.trans hNear)
  have hOrd := checked_distanceLe_absolute ha (gaussianRat c) (gaussianRat c₀) (e+k)
    (add_nonneg he.le hk) h2
  have hNorm : ‖gaussianRat c-gaussianRat c₀‖ ≤ ((e+k : ℚ) : ℝ) := by
    simpa only [dist_eq_norm] using hOrd
  have hRe : |c.1-c₀.1| ≤ k+e := by
    have h := (Complex.abs_re_le_norm (gaussianRat c-gaussianRat c₀)).trans hNorm
    exact_mod_cast (show (|(c.1 : ℝ)-(c₀.1 : ℝ)| : ℝ) ≤ ((k+e : ℚ) : ℝ) by
      simpa only [gaussianRat,Complex.sub_re,Rat.cast_add,add_comm] using h)
  have hIm : |c.2-c₀.2| ≤ k+e := by
    have h := (Complex.abs_im_le_norm (gaussianRat c-gaussianRat c₀)).trans hNorm
    exact_mod_cast (show (|(c.2 : ℝ)-(c₀.2 : ℝ)| : ℝ) ≤ ((k+e : ℚ) : ℝ) by
      simpa only [gaussianRat,Complex.sub_im,Rat.cast_add,add_comm] using h)
  have hRe' := abs_le.mp hRe
  have hIm' := abs_le.mp hIm
  obtain ⟨q,hq,hqA,hC⟩ := cohen_refine_strict_interior_point p a ha (haB.trans hbP) i j hij s t c
    (by linarith [hLi,hRe'.1]) (by linarith [hRi,hRe'.2])
    (by linarith [hLj,hIm'.1]) (by linarith [hRj,hIm'.2]) e he
  have hQ : imageCondition q ≤ F.toFun a := by
    change imageCondition q ≤ baseEmbed (valuedCohen B (I × ℕ)) a
    exact (baseEmbed_reflects_mask_r427 q a).mpr hqA.le
  have hX := cutOn_mono930 (ComplexBits.map_cutOn F hxA) hQ
  have hZ := intervalPointBits_valid i j s t (imageCondition q)
  have hC₁ := ComplexBits.checked_cutOn (B := CohenBA B (I × ℕ)) (gaussianRat c) (imageCondition q)
  have hC₂ := ComplexBits.checked_cutOn (B := CohenBA B (I × ℕ)) (gaussianRat c₀) (imageCondition q)
  have hA' := hQ.trans (F.monotone h1)
  rw [map_distanceLe,ComplexBits.map_checked] at hA'
  have hB' := hQ.trans (F.monotone h2)
  simp only [map_distanceLe,ComplexBits.map_checked] at hB'
  exact ⟨q,hq,distanceLe_triangle hZ hC₁ hX he.le he.le hC hA',
    distanceLe_triangle hZ hC₁ hC₂ he.le (add_nonneg he.le hk) hC hB'⟩

end JSP000930.Negative.Cohen
