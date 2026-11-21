import JSP000930CohenWordPairMetric

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B I K : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype K]

def centerComponent (c : ℚ × ℚ) : Bool → ℚ
  | false => c.1
  | true => c.2

set_option maxHeartbeats 600000 in
theorem cohen_refine_many_strict_interior_points
    (p : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbP : b ≤ p.mask)
    (route : K × Bool → I) (hRoute : Function.Injective route)
    (s : K × Bool → Interval) (c : K → ℚ × ℚ) (e : K → ℚ) (he : ∀ k,0 < e k)
    (hIn : ∀ k j,
      ((s (k,j)).follow (completeRowWord p.trace (route (k,j)))).left < centerComponent (c k) j ∧
      centerComponent (c k) j < ((s (k,j)).follow (completeRowWord p.trace (route (k,j)))).right) :
    ∃ q : CohenTotal B (I × ℕ), q ≤ p ∧ q.mask = b ∧
      ∀ k,imageCondition q ≤ distanceLe
        (intervalPointBits B (route (k,false)) (route (k,true)) (s (k,false)) (s (k,true)))
        (ComplexBits.checked (gaussianRat (c k))) (e k) := by
  classical
  let t (j : K × Bool) := (s j).follow (completeRowWord p.trace (route j))
  have hv (j : K × Bool) : ∃ v : List Bool,centerComponent (c j.1) j.2-e j.1/4 <
      ((t j).follow v).left ∧ ((t j).follow v).right < centerComponent (c j.1) j.2+e j.1/4 := by
    have hh := hIn j.1 j.2
    have hε : (0 : ℝ) < (e j.1/4 : ℚ) := by exact_mod_cast (show 0 < e j.1/4 by linarith [he j.1])
    obtain ⟨v,hL,hR⟩ := follow_inside_neighborhood (t j)
      (x := (centerComponent (c j.1) j.2 : ℝ))
      (by exact_mod_cast hh.1) (by exact_mod_cast hh.2) hε
    exact ⟨v,
      by exact_mod_cast (show ((centerComponent (c j.1) j.2-e j.1/4 : ℚ) : ℝ) <
        (((t j).follow v).left : ℝ) by simpa only [Rat.cast_sub] using hL),
      by exact_mod_cast (show (((t j).follow v).right : ℝ) <
        ((centerComponent (c j.1) j.2+e j.1/4 : ℚ) : ℝ) by simpa only [Rat.cast_add] using hR)⟩
  choose w hw using hv
  let F : Finset I := Finset.univ.image route
  let W (i : I) : List Bool := if h : ∃ j,route j = i then w (Classical.choose h) else []
  have hW (j) : W (route j) = w j := by
    let h : ∃ k,route k = route j := ⟨j,rfl⟩
    have hh : Classical.choose h = j := hRoute (Classical.choose_spec h)
    simp only [W,dite_eq_left h,hh]
  obtain ⟨q,hqp,hqB,hWords⟩ := cohen_append_on_earlier_mark p b hb hbP F W
  have hWord (j : K × Bool) : imageCondition q ≤ wordValue B (route j)
      (completeRowWord p.trace (route j) ++ w j) := by
    have hj : route j ∈ F := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    apply image_le_wordValue
    simpa only [hW j] using hWords (route j) hj
  refine ⟨q,hqp,hqB,?_⟩
  intro k
  apply distanceLe_from_narrow_cohen_words _ _ _ _ _ _ _ _ (he k) _ (hWord (k,false)) (hWord (k,true))
  · simpa only [t,Interval.follow_append,centerComponent] using (hw (k,false)).1
  · simpa only [t,Interval.follow_append,centerComponent] using (hw (k,false)).2
  · simpa only [t,Interval.follow_append,centerComponent] using (hw (k,true)).1
  · simpa only [t,Interval.follow_append,centerComponent] using (hw (k,true)).2

end JSP000930.Negative.Cohen
