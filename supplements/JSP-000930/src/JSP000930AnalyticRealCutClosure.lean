import JSP000930AnalyticRealNat

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem properCutOn_mono {p q : B} {β : RatPresentation → B}
    (hpq : p ≤ q) (h : ProperCutOn q β) : ProperCutOn p β := by
  exact ⟨hpq.trans h.1,hpq.trans h.2.1,
    fun a b hab => (inf_le_inf_right _ hpq).trans (h.2.2.1 a b hab),
    fun a => (inf_le_inf_right _ hpq).trans (h.2.2.2 a)⟩

theorem addCutBits_properCut (u v : RatPresentation → B) (p : B)
    (hu : ProperCutOn p u) (hv : ProperCutOn p v) :
    ProperCutOn p (addCutBits u v) := by
  refine ⟨addCutBits_nonempty_below u v p hu.1 hv.1,?_,?_,?_⟩
  · have hp : p ≤ p ⊓ ((⨆ a : RatPresentation, (u a)ᶜ) ⊓
      (⨆ b : RatPresentation, (v b)ᶜ)) := le_inf le_rfl (le_inf hu.2.1 hv.2.1)
    apply hp.trans
    rw [iSup_inf_eq,inf_iSup_eq]
    refine iSup_le fun a => ?_
    rw [inf_iSup_eq,inf_iSup_eq]
    refine iSup_le fun b => ?_
    obtain ⟨q,hq⟩ := ratPresentation_value_surjective (a.value+b.value)
    let e : B := p ⊓ ((u a)ᶜ ⊓ (v b)ᶜ)
    have he : e ≤ p := inf_le_left
    have hU := properCutOn_mono he hu
    have hV := properCutOn_mono he hv
    exact (addCutBits_bounded_below u v e a b q hq
       (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
       (fun r hr => hU.2.2.1 a r hr) (fun r hr => hV.2.2.1 b r hr)).trans
      (le_iSup (fun q => (addCutBits u v q)ᶜ) q)
  · intro q r h
    exact inf_le_right.trans (addCutBits_downward u v h)
  · intro q
    exact inf_le_right.trans_eq (addCutBits_rounded u v q)

theorem negCutBits_properCut (u : RatPresentation → B) (p : B)
    (hu : ProperCutOn p u) : ProperCutOn p (negCutBits u) := by
  refine ⟨?_,?_,?_,?_⟩
  · apply hu.2.1.trans
    refine iSup_le fun r => ?_
    obtain ⟨q,hq⟩ := ratPresentation_value_surjective (-r.value-1)
    have hlt : q.value < -r.value := by rw [hq]; linarith
    exact le_iSup_of_le q (le_iSup_of_le r (le_iSup (fun _ : q.value < -r.value => (u r)ᶜ) hlt))
  · have hp : p ≤ p ⊓ (⨆ r : RatPresentation, u r) := le_inf le_rfl hu.1
    apply hp.trans
    rw [inf_iSup_eq]
    refine iSup_le fun r => ?_
    obtain ⟨q,hq⟩ := ratPresentation_value_surjective (-r.value)
    apply le_iSup_of_le q
    apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff_inf_le,negCutBits,inf_iSup_eq]
    refine iSup_le fun t => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun hqt => ?_
    have htr : t.value ≤ r.value := by rw [hq] at hqt; linarith
    have h : p ⊓ u r ≤ u t := hu.2.2.1 t r htr
    exact (inf_le_inf_right _ h).trans (by simp)
  · intro q r hqr
    exact inf_le_right.trans (negCutBits_downward u hqr)
  · intro q
    exact inf_le_right.trans_eq (negCutBits_rounded u q)

end JSP000930.BooleanAnalysis
