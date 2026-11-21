import JSP000930AnalyticRealCutClosure
import JSP000930AnalyticRealMul
import JSP000930AnalyticCutMulMetric

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem properCutOn_boxCover {p : B} {u : RatPresentation → B} (h : ProperCutOn p u) :
    p ≤ ⨆ a : RatPresentation, ⨆ b : RatPresentation, intervalBits u a b := by
  apply (le_inf h.1 h.2.1).trans
  rw [iSup_inf_eq]
  refine iSup_le fun a => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun t => ?_
  obtain ⟨b,hb⟩ := ratPresentation_value_surjective (t.value+1)
  have htb : t.value < b.value := by rw [hb]; linarith
  apply le_iSup_of_le a
  apply le_iSup_of_le b
  unfold intervalBits
  exact inf_le_inf_left _ (le_iSup_of_le t (le_iSup (fun _ : t.value < b.value => (u t)ᶜ) htb))

theorem properCutOn_incompatible_upperLower {p s : B} {u : RatPresentation → B}
    (hp : ProperCutOn p u) (hsp : s ≤ p) {a b c : RatPresentation}
    (hlo : s ≤ u a) (hhi : s ≤ intervalBits u b c) (hca : c.value ≤ a.value) :
    s ≤ ⊥ := by
  have hbound : s ≤ ⨆ t : RatPresentation, ⨆ (_ : t.value<c.value), (u t)ᶜ :=
    hhi.trans inf_le_right
  apply (le_inf le_rfl hbound).trans
  rw [inf_iSup_eq]
  refine iSup_le fun t => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun ht => ?_
  have hu : s ≤ u t := (le_inf hsp hlo).trans (hp.2.2.1 t a (ht.le.trans hca))
  exact (inf_le_inf_right _ hu).trans (by simp)

theorem properCutOn_boxIntersects {p s : B} {u : RatPresentation → B}
    (hp : ProperCutOn p u) (hsp : s ≤ p) (hs : s ≠ ⊥)
    {a b c d : RatPresentation} (ha : s ≤ intervalBits u a b) (hc : s ≤ intervalBits u c d) :
    ∃ x : ℚ, a.value ≤ x ∧ x ≤ b.value ∧ c.value ≤ x ∧ x ≤ d.value := by
  have hab : a.value < b.value := by
    by_contra hh
    exact hs (le_bot_iff.mp
      (properCutOn_incompatible_upperLower hp hsp (ha.trans inf_le_left) ha (le_of_not_gt hh)))
  have hcd : c.value < d.value := by
    by_contra hh
    exact hs (le_bot_iff.mp
      (properCutOn_incompatible_upperLower hp hsp (hc.trans inf_le_left) hc (le_of_not_gt hh)))
  have had : a.value < d.value := by
    by_contra hh
    exact hs (le_bot_iff.mp
      (properCutOn_incompatible_upperLower hp hsp (ha.trans inf_le_left) hc (le_of_not_gt hh)))
  have hcb : c.value < b.value := by
    by_contra hh
    exact hs (le_bot_iff.mp
      (properCutOn_incompatible_upperLower hp hsp (hc.trans inf_le_left) ha (le_of_not_gt hh)))
  refine ⟨max a.value c.value,le_max_left _ _,max_le hab.le hcb.le,
    le_max_right _ _,max_le had.le hcd.le⟩

private theorem fourCorners_upper {q a b c d x y : ℚ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d)
    (hac : a*c < q) (had : a*d < q) (hbc : b*c < q) (hbd : b*d < q) :
    x*y < q := by
  have h : (-(q : ℝ)) < (-(x : ℝ)) * (y : ℝ) := by
    refine strictLower_fourCorners (a := -(b : ℝ)) (b := -(a : ℝ))
      (c := (c : ℝ)) (d := (d : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · apply neg_le_neg
      exact_mod_cast hxb
    · apply neg_le_neg
      exact_mod_cast hax
    · exact_mod_cast hcy
    · exact_mod_cast hyd
    · rw [neg_mul]
      apply neg_lt_neg
      exact_mod_cast hbc
    · rw [neg_mul]
      apply neg_lt_neg
      exact_mod_cast hbd
    · rw [neg_mul]
      apply neg_lt_neg
      exact_mod_cast hac
    · rw [neg_mul]
      apply neg_lt_neg
      exact_mod_cast had
  rw [neg_mul,neg_lt_neg_iff] at h
  exact_mod_cast h

private theorem mulCut_nonemptyFromBoxes (u v : RatPresentation → B)
    (a b c d : RatPresentation) :
    intervalBits u a b ⊓ intervalBits v c d ≤ ⨆ q : RatPresentation, mulCutBits u v q := by
  let m := min (min (a.value*c.value) (a.value*d.value))
    (min (b.value*c.value) (b.value*d.value))
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (m-1)
  have hqm : q.value < m := by rw [hq]; linarith
  have hh : belowRectangleProducts q a b c d :=
    ⟨hqm.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
     hqm.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
     hqm.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
     hqm.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  exact le_iSup_of_le q (le_iSup_of_le a (le_iSup_of_le b
    (le_iSup_of_le c (le_iSup_of_le d (le_iSup (fun _ : belowRectangleProducts q a b c d =>
      intervalBits u a b ⊓ intervalBits v c d) hh)))))

theorem mulCut_excludes_fromBoxes {p : B} {u v : RatPresentation → B}
    (hu : ProperCutOn p u) (hv : ProperCutOn p v) (a b c d q : RatPresentation)
    (hac : a.value*c.value < q.value) (had : a.value*d.value < q.value)
    (hbc : b.value*c.value < q.value) (hbd : b.value*d.value < q.value) :
    p ⊓ (intervalBits u a b ⊓ intervalBits v c d) ≤ (mulCutBits u v q)ᶜ := by
  let s : B := p ⊓ (intervalBits u a b ⊓ intervalBits v c d)
  change s ≤ _
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le,mulCutBits,inf_iSup_eq]
  refine iSup_le fun A => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun C => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun D => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun E => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun hco => ?_
  let t : B := s ⊓ (intervalBits u A C ⊓ intervalBits v D E)
  change t ≤ ⊥
  by_contra ht
  have htn : t ≠ ⊥ := fun eq => ht (le_of_eq eq)
  have htp : t ≤ p := inf_le_left.trans inf_le_left
  have hua : t ≤ intervalBits u a b := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hvb : t ≤ intervalBits v c d := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have huA : t ≤ intervalBits u A C := inf_le_right.trans inf_le_left
  have hvD : t ≤ intervalBits v D E := inf_le_right.trans inf_le_right
  obtain ⟨x,hax,hxb,hAx,hxC⟩ := properCutOn_boxIntersects hu htp htn hua huA
  obtain ⟨y,hcy,hyd,hDy,hyE⟩ := properCutOn_boxIntersects hv htp htn hvb hvD
  have hUpper : x*y < q.value := fourCorners_upper hax hxb hcy hyd
    hac had hbc hbd
  have hLower : q.value < x*y := by
    have hh : (q.value : ℝ) < (x : ℝ)*(y : ℝ) := by
      refine strictLower_fourCorners (a := (A.value : ℝ)) (b := (C.value : ℝ))
        (c := (D.value : ℝ)) (d := (E.value : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact_mod_cast hAx
      · exact_mod_cast hxC
      · exact_mod_cast hDy
      · exact_mod_cast hyE
      · exact_mod_cast hco.1
      · exact_mod_cast hco.2.1
      · exact_mod_cast hco.2.2.1
      · exact_mod_cast hco.2.2.2
    exact_mod_cast hh
  exact (not_lt_of_gt hUpper) hLower

private theorem mulCut_properFromBoxes {p : B} {u v : RatPresentation → B}
    (hu : ProperCutOn p u) (hv : ProperCutOn p v) (a b c d : RatPresentation) :
    p ⊓ (intervalBits u a b ⊓ intervalBits v c d) ≤
      ⨆ q : RatPresentation, (mulCutBits u v q)ᶜ := by
  let m := max (max (a.value*c.value) (a.value*d.value))
    (max (b.value*c.value) (b.value*d.value))
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (m+1)
  have hmq : m < q.value := by rw [hq]; linarith
  apply le_iSup_of_le q
  exact mulCut_excludes_fromBoxes hu hv a b c d q
    (((le_max_left _ _).trans (le_max_left _ _)).trans_lt hmq)
    (((le_max_right _ _).trans (le_max_left _ _)).trans_lt hmq)
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hmq)
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hmq)

theorem mulCutBits_properCut (u v : RatPresentation → B) (p : B)
    (hu : ProperCutOn p u) (hv : ProperCutOn p v) : ProperCutOn p (mulCutBits u v) := by
  let U := ⨆ a : RatPresentation, ⨆ b : RatPresentation, intervalBits u a b
  let V := ⨆ c : RatPresentation, ⨆ d : RatPresentation, intervalBits v c d
  have hU : p ≤ U := properCutOn_boxCover hu
  have hV : p ≤ V := properCutOn_boxCover hv
  refine ⟨?_,?_,?_,?_⟩
  · apply (le_inf hU hV).trans
    dsimp [U,V]
    rw [iSup_inf_eq]
    refine iSup_le fun a => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun b => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun c => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d => mulCut_nonemptyFromBoxes u v a b c d
  · apply (le_inf le_rfl (le_inf hU hV)).trans
    dsimp [U,V]
    rw [iSup_inf_eq,inf_iSup_eq]
    refine iSup_le fun a => ?_
    rw [iSup_inf_eq,inf_iSup_eq]
    refine iSup_le fun b => ?_
    rw [inf_iSup_eq,inf_iSup_eq]
    refine iSup_le fun c => ?_
    rw [inf_iSup_eq,inf_iSup_eq]
    refine iSup_le fun d => mulCut_properFromBoxes hu hv a b c d
  · intro q r hqr
    exact inf_le_right.trans (mulCutBits_downward u v hqr)
  · intro q
    exact inf_le_right.trans_eq (mulCutBits_rounded u v q)

end JSP000930.BooleanAnalysis
