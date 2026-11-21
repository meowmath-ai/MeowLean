import JSP000930CohenMarkedWordReplacements
import JSP000930GaussianRationalSeed
import JSP000930MixedRectangleDistance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.Positive JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000933.BooleanCompletion JSP000933.BooleanNames JSP000933.MarkedForcing

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def intervalPointBits (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (i j : I) (s t : Interval) : ComplexBits (CohenBA B (I × ℕ)) :=
  ⟨intervalCutBits i s,intervalCutBits j t⟩

theorem intervalPointBits_valid (i j : I) (s t : Interval) (m : CohenBA B (I × ℕ)) :
    (intervalPointBits B i j s t).CutOn m :=
  ⟨JSP000930.BooleanAnalysis.properCutOn_mono le_top (intervalCut_proper i s),
   JSP000930.BooleanAnalysis.properCutOn_mono le_top (intervalCut_proper j t)⟩

theorem checked_rationalEnclosure (x : ℝ) (a b : RatPresentation)
    (m : B) (ha : (a.value : ℝ) < x) (hb : x ≤ (b.value : ℝ)) :
    RationalEncloses (checkedRealBits x) a b m := by
  constructor
  · simpa only [checkedRealBits,JSP000933.PositiveForcing.crispTruth,ite_eq_left ha] using (le_top : m ≤ ⊤)
  · simpa only [checkedRealBits,JSP000933.PositiveForcing.crispTruth,ite_eq_right (not_lt_of_ge hb),compl_bot] using
      (le_top : m ≤ ⊤)

set_option maxHeartbeats 400000 in
theorem cohen_refine_strict_interior_point
    (p : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbP : b ≤ p.mask)
    (i j : I) (hij : i ≠ j) (s t : Interval) (c : ℚ × ℚ)
    (hLi : (s.follow (completeRowWord p.trace i)).left < c.1)
    (hRi : c.1 < (s.follow (completeRowWord p.trace i)).right)
    (hLj : (t.follow (completeRowWord p.trace j)).left < c.2)
    (hRj : c.2 < (t.follow (completeRowWord p.trace j)).right)
    (e : ℚ) (he : 0 < e) :
    ∃ q : CohenTotal B (I × ℕ),q ≤ p ∧ q.mask = b ∧
      imageCondition q ≤ distanceLe (intervalPointBits B i j s t)
        (ComplexBits.checked (gaussianRat c)) e := by
  classical
  have hQuarter : (0 : ℝ) < (e / 4 : ℚ) := by
    exact_mod_cast (show (0 : ℚ) < e / 4 by linarith)
  obtain ⟨wi,hwiL,hwiR⟩ := follow_inside_neighborhood (s.follow (completeRowWord p.trace i))
    (x := (c.1 : ℝ)) (by exact_mod_cast hLi) (by exact_mod_cast hRi) hQuarter
  obtain ⟨wj,hwjL,hwjR⟩ := follow_inside_neighborhood (t.follow (completeRowWord p.trace j))
    (x := (c.2 : ℝ)) (by exact_mod_cast hLj) (by exact_mod_cast hRj) hQuarter
  obtain ⟨a,ha⟩ := ratPresentation_value_surjective (c.1 - e/4)
  obtain ⟨A,hA⟩ := ratPresentation_value_surjective (c.1 + e/4)
  obtain ⟨d,hd⟩ := ratPresentation_value_surjective (c.2 - e/4)
  obtain ⟨D,hD⟩ := ratPresentation_value_surjective (c.2 + e/4)
  let F : Finset I := {i,j}
  let tail (k : I) := if k = i then wi else wj
  obtain ⟨q,hqp,hqB,hW⟩ := cohen_append_on_earlier_mark p b hb hbP F tail
  have hi : i ∈ F := by simp [F]
  have hj : j ∈ F := by simp [F]
  let v := completeRowWord p.trace i ++ wi
  let w := completeRowWord p.trace j ++ wj
  have hv : imageCondition q ≤ wordValue B i v := image_le_wordValue q i v (by
    simpa only [v,tail,ite_eq_left rfl] using hW i hi)
  have hw : imageCondition q ≤ wordValue B j w := image_le_wordValue q j w (by
    simpa only [w,tail,ite_eq_right hij.symm] using hW j hj)
  have hVa : a.value < (s.follow v).left := by
    dsimp only [v]; rw [ha,Interval.follow_append]
    exact_mod_cast (show ((c.1-e/4 : ℚ) : ℝ) <
      (((s.follow (completeRowWord p.trace i)).follow wi).left : ℝ) by
      simpa only [Rat.cast_sub] using hwiL)
  have hVA : (s.follow v).right ≤ A.value := by
    dsimp only [v]; rw [hA,Interval.follow_append]
    exact_mod_cast (show (((s.follow (completeRowWord p.trace i)).follow wi).right : ℝ) ≤
      ((c.1+e/4 : ℚ) : ℝ) by simpa only [Rat.cast_add] using hwiR.le)
  have hWd : d.value < (t.follow w).left := by
    dsimp only [w]; rw [hd,Interval.follow_append]
    exact_mod_cast (show ((c.2-e/4 : ℚ) : ℝ) <
      (((t.follow (completeRowWord p.trace j)).follow wj).left : ℝ) by
      simpa only [Rat.cast_sub] using hwjL)
  have hWD : (t.follow w).right ≤ D.value := by
    dsimp only [w]; rw [hD,Interval.follow_append]
    exact_mod_cast (show (((t.follow (completeRowWord p.trace j)).follow wj).right : ℝ) ≤
      ((c.2+e/4 : ℚ) : ℝ) by simpa only [Rat.cast_add] using hwjR.le)
  let x := intervalPointBits B i j s t
  let y := ComplexBits.checked (B := CohenBA B (I × ℕ)) (gaussianRat c)
  let m := imageCondition q
  have hxr : RationalEncloses x.re a A m :=
    ⟨hv.trans (intervalCut_below_left i s v a hVa),hv.trans (intervalCut_above_right i s v A hVA)⟩
  have hxi : RationalEncloses x.im d D m :=
    ⟨hw.trans (intervalCut_below_left j t w d hWd),hw.trans (intervalCut_above_right j t w D hWD)⟩
  have hyr : RationalEncloses y.re a A m := checked_rationalEnclosure _ _ _ m
    (by change (a.value : ℝ) < (c.1 : ℝ); rw [ha]; exact_mod_cast (show c.1-e/4 < c.1 by linarith))
    (by change (c.1 : ℝ) ≤ (A.value : ℝ); rw [hA]; exact_mod_cast (show c.1 ≤ c.1+e/4 by linarith))
  have hyi : RationalEncloses y.im d D m := checked_rationalEnclosure _ _ _ m
    (by change (d.value : ℝ) < (c.2 : ℝ); rw [hd]; exact_mod_cast (show c.2-e/4 < c.2 by linarith))
    (by change (c.2 : ℝ) ≤ (D.value : ℝ); rw [hD]; exact_mod_cast (show c.2 ≤ c.2+e/4 by linarith))
  exact ⟨q,hqp,hqB,distanceLe_of_common_box x y m (intervalPointBits_valid i j s t m)
    (ComplexBits.checked_cutOn _ _) a A d D hxr hxi hyr hyi e (by rw [ha,hA,hd,hD]; ring_nf <;> exact le_rfl)⟩

end JSP000930.Negative.Cohen
