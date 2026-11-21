import JSP000930AnalyticRoundedLimit

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def addCutBits (u v : RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ r : RatPresentation, ⨆ s : RatPresentation, ⨆ (_ : q.value < r.value+s.value),
    u r ⊓ v s

theorem addCutBits_downward (u v : RatPresentation → B) {q t : RatPresentation}
    (h : q.value ≤ t.value) : addCutBits u v t ≤ addCutBits u v q := by
  unfold addCutBits
  refine iSup_le fun r => iSup_le fun s => iSup_le fun ht => ?_
  exact le_iSup_of_le r (le_iSup_of_le s (le_iSup (fun _ : q.value < r.value + s.value => u r ⊓ v s) (h.trans_lt ht)))

theorem addCutBits_rounded (u v : RatPresentation → B) (q : RatPresentation) :
    addCutBits u v q = ⨆ t : RatPresentation, ⨆ (_ : q.value < t.value), addCutBits u v t := by
  apply le_antisymm
  · unfold addCutBits
    refine iSup_le fun r => iSup_le fun s => iSup_le fun hq => ?_
    obtain ⟨t,ht⟩ := ratPresentation_value_surjective ((q.value+r.value+s.value)/2)
    have hqt : q.value < t.value := by rw [ht]; linarith
    have htr : t.value < r.value+s.value := by rw [ht]; linarith
    exact le_iSup_of_le t (le_iSup_of_le hqt
      (le_iSup_of_le r (le_iSup_of_le s (le_iSup (fun _ : t.value < r.value + s.value => u r ⊓ v s) htr))))
  · refine iSup_le fun t => iSup_le fun ht => ?_
    exact addCutBits_downward u v ht.le

theorem addCutBits_nonempty_below (u v : RatPresentation → B) (p : B)
    (hu : p ≤ ⨆ r : RatPresentation, u r) (hv : p ≤ ⨆ s : RatPresentation, v s) :
    p ≤ ⨆ q : RatPresentation, addCutBits u v q := by
  apply (le_inf hu hv).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro r
  rw [inf_iSup_eq]
  apply iSup_le
  intro s
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (r.value+s.value-1)
  have hlt : q.value < r.value+s.value := by rw [hq]; linarith
  exact le_iSup_of_le q (le_iSup_of_le r (le_iSup_of_le s (le_iSup (fun _ : q.value < r.value + s.value => u r ⊓ v s) hlt)))

theorem addCutBits_bounded_below (u v : RatPresentation → B) (p : B)
    (a b q : RatPresentation) (hq : q.value = a.value+b.value)
    (ha : p ≤ (u a)ᶜ) (hb : p ≤ (v b)ᶜ)
    (hu : ∀ r : RatPresentation, a.value ≤ r.value → p ⊓ u r ≤ u a)
    (hv : ∀ s : RatPresentation, b.value ≤ s.value → p ⊓ v s ≤ v b) :
    p ≤ (addCutBits u v q)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le, addCutBits, inf_iSup_eq]
  apply iSup_le
  intro r
  rw [inf_iSup_eq]
  apply iSup_le
  intro s
  rw [inf_iSup_eq]
  apply iSup_le
  intro h
  have hr : a.value ≤ r.value ∨ b.value ≤ s.value := by
    by_contra hh
    push Not at hh
    linarith [hh.1, hh.2]
  have hp : p ⊓ (u r ⊓ v s) ≤ p := inf_le_left
  rcases hr with hr | hr
  · have hU : p ⊓ (u r ⊓ v s) ≤ u a :=
      (le_inf hp (inf_le_right.trans inf_le_left)).trans (hu r hr)
    exact (le_inf (hp.trans ha) hU).trans (by simp)
  · have hV : p ⊓ (u r ⊓ v s) ≤ v b :=
      (le_inf hp (inf_le_right.trans inf_le_right)).trans (hv s hr)
    exact (le_inf (hp.trans hb) hV).trans (by simp)

noncomputable def addCutName (u v : RatPresentation → B) : bSet B :=
  weightedRationalSet (addCutBits u v)

theorem addCutName_membership (u v : RatPresentation → B) (q : RatPresentation) :
    (ratName q ∈ᴮ addCutName u v) = addCutBits u v q :=
  ratName_mem_weightedRationalSet _ q

end JSP000930.BooleanAnalysis
