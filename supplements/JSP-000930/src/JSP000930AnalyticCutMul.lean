import JSP000930AnalyticCutAdd

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def intervalBits (u : RatPresentation → B) (a b : RatPresentation) : B :=
  u a ⊓ (⨆ t : RatPresentation, ⨆ (_ : t.value < b.value), (u t)ᶜ)

def belowRectangleProducts (q a b c d : RatPresentation) : Prop :=
  q.value < a.value*c.value ∧ q.value < a.value*d.value ∧
    q.value < b.value*c.value ∧ q.value < b.value*d.value

noncomputable def mulCutBits (u v : RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ a : RatPresentation, ⨆ b : RatPresentation, ⨆ c : RatPresentation, ⨆ d : RatPresentation,
    ⨆ (_ : belowRectangleProducts q a b c d), intervalBits u a b ⊓ intervalBits v c d

theorem mulCutBits_downward (u v : RatPresentation → B) {q t : RatPresentation}
    (h : q.value ≤ t.value) : mulCutBits u v t ≤ mulCutBits u v q := by
  unfold mulCutBits
  refine iSup_le fun a => iSup_le fun b => iSup_le fun c => iSup_le fun d => iSup_le fun ht => ?_
  have hq : belowRectangleProducts q a b c d :=
    ⟨h.trans_lt ht.1,h.trans_lt ht.2.1,h.trans_lt ht.2.2.1,h.trans_lt ht.2.2.2⟩
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le c (le_iSup_of_le d (le_iSup (fun _ : belowRectangleProducts q a b c d => intervalBits u a b ⊓ intervalBits v c d) hq))))

theorem mulCutBits_rounded (u v : RatPresentation → B) (q : RatPresentation) :
    mulCutBits u v q = ⨆ t : RatPresentation, ⨆ (_ : q.value < t.value), mulCutBits u v t := by
  apply le_antisymm
  · unfold mulCutBits
    refine iSup_le fun a => iSup_le fun b => iSup_le fun c => iSup_le fun d => iSup_le fun hq => ?_
    let m := min (min (a.value*c.value) (a.value*d.value))
      (min (b.value*c.value) (b.value*d.value))
    have hm : q.value < m :=
      lt_min (lt_min hq.1 hq.2.1) (lt_min hq.2.2.1 hq.2.2.2)
    obtain ⟨t,ht⟩ := ratPresentation_value_surjective ((q.value+m)/2)
    have hqt : q.value < t.value := by rw [ht]; linarith
    have htm : t.value < m := by rw [ht]; linarith
    have ht' : belowRectangleProducts t a b c d := by
      refine ⟨?_,?_,?_,?_⟩
      · exact htm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      · exact htm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      · exact htm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      · exact htm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact le_iSup_of_le t (le_iSup_of_le hqt
      (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le c (le_iSup_of_le d (le_iSup (fun _ : belowRectangleProducts t a b c d => intervalBits u a b ⊓ intervalBits v c d) ht'))))))
  · refine iSup_le fun t => iSup_le fun ht => ?_
    exact mulCutBits_downward u v ht.le

noncomputable def mulCutName (u v : RatPresentation → B) : bSet B :=
  weightedRationalSet (mulCutBits u v)

theorem mulCutName_membership (u v : RatPresentation → B) (q : RatPresentation) :
    (ratName q ∈ᴮ mulCutName u v) = mulCutBits u v q :=
  ratName_mem_weightedRationalSet _ q

theorem strictLower_fourCorners {q a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d)
    (hac : q < a*c) (had : q < a*d) (hbc : q < b*c) (hbd : q < b*d) :
    q < x*y := by
  have hline (k : ℝ) (hkc : q < k*c) (hkd : q < k*d) : q < k*y := by
    by_cases hk : 0 ≤ k
    · exact hkc.trans_le (mul_le_mul_of_nonneg_left hcy hk)
    · exact hkd.trans_le (mul_le_mul_of_nonpos_left hyd (le_of_not_ge hk))
  by_cases hy : 0 ≤ y
  · exact (hline a hac had).trans_le (mul_le_mul_of_nonneg_right hax hy)
  · exact (hline b hbc hbd).trans_le (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hy))

end JSP000930.BooleanAnalysis
