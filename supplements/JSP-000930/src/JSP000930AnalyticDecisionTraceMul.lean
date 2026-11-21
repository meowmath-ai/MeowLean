import JSP000930AnalyticDecisionTrace

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanNames JSP000933.PositiveForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem CutDecisionTrace.mul {p : ℕ → B} (h : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (hU : ProperCutOn m u) (hV : ProperCutOn m v) :
    CutDecisionTrace p (mulCutBits u v) (x*y) := by
  constructor
  · intro q hq
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hcorners⟩ := exists_small_rationalBox_products hq
    obtain ⟨n,hn⟩ := eventuallyMeet h (hu.interval h a b ha hb) (hv.interval h c d hc hd)
    exact ⟨n,hn.trans (le_iSup_of_le a (le_iSup_of_le b
      (le_iSup_of_le c (le_iSup_of_le d (le_iSup (fun _ : belowRectangleProducts q a b c d =>
        intervalBits u a b ⊓ intervalBits v c d) hcorners)))))⟩
  · intro q hq
    have hneg : (q.opposite.value : ℝ) < (-x)*y := by
      rw [RatPresentation.opposite_value,Rat.cast_neg,neg_mul]
      exact neg_lt_neg hq
    obtain ⟨a0,b0,c,d,ha0,hb0,hc,hd,hcor⟩ := exists_small_rationalBox_products hneg
    let a := b0.opposite
    let b := a0.opposite
    have ha : (a.value : ℝ) < x := by
      dsimp only [a]
      rw [RatPresentation.opposite_value,Rat.cast_neg]
      linarith
    have hb : x < (b.value : ℝ) := by
      dsimp only [b]
      rw [RatPresentation.opposite_value,Rat.cast_neg]
      linarith
    have hac : a.value*c.value < q.value := by
      have hh := hcor.2.2.1
      rw [RatPresentation.opposite_value] at hh
      simp only [a,RatPresentation.opposite_value,neg_mul]
      linarith
    have had : a.value*d.value < q.value := by
      have hh := hcor.2.2.2
      rw [RatPresentation.opposite_value] at hh
      simp only [a,RatPresentation.opposite_value,neg_mul]
      linarith
    have hbc : b.value*c.value < q.value := by
      have hh := hcor.1
      rw [RatPresentation.opposite_value] at hh
      simp only [b,RatPresentation.opposite_value,neg_mul]
      linarith
    have hbd : b.value*d.value < q.value := by
      have hh := hcor.2.1
      rw [RatPresentation.opposite_value] at hh
      simp only [b,RatPresentation.opposite_value,neg_mul]
      linarith
    obtain ⟨n,hn⟩ := eventuallyMeet h (hu.interval h a b ha hb) (hv.interval h c d hc hd)
    exact ⟨n,(le_inf (hpm n) hn).trans
      (mulCut_excludes_fromBoxes hU hV a b c d q hac had hbc hbd)⟩

theorem checkedRealBits_traces (p : ℕ → B) (x : ℝ) :
    CutDecisionTrace p (checkedRealBits x) x := by
  constructor
  · intro r hr
    exact ⟨0,by simp [checkedRealBits,crispTruth,hr]⟩
  · intro r hr
    exact ⟨0,by simp [checkedRealBits,crispTruth,not_lt_of_gt hr]⟩

end JSP000930.BooleanAnalysis
