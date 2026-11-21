import JSP000930PositiveStrictRationalCoefficientGap
import JSP000930PositiveTaylorBitCode

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem orient_boolean_mask_difference (p u v : B)
    (h : p ⊓ u ≠ p ⊓ v) :
    ∃ d : B, d ≠ ⊥ ∧ d ≤ p ∧
      ((d ≤ u ∧ d ≤ vᶜ) ∨ (d ≤ v ∧ d ≤ uᶜ)) := by
  have hCase : ¬ (p ⊓ u ≤ p ⊓ v) ∨ ¬ (p ⊓ v ≤ p ⊓ u) := by
    by_contra! hn
    exact h (le_antisymm hn.1 hn.2)
  have step (a b : B) (hn : ¬ (p ⊓ a ≤ p ⊓ b)) :
      ∃ d : B, d ≠ ⊥ ∧ d ≤ p ∧ d ≤ a ∧ d ≤ bᶜ := by
    let d := (p ⊓ a) ⊓ bᶜ
    refine ⟨d,?_,inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right,inf_le_right⟩
    intro hb
    apply hn
    exact le_inf inf_le_left
      (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr hb.le))
  rcases hCase with hu | hv
  · obtain ⟨d,hd,hp,ha,hb⟩ := step u v hu
    exact ⟨d,hd,hp,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨d,hd,hp,ha,hb⟩ := step v u hv
    exact ⟨d,hd,hp,Or.inr ⟨ha,hb⟩⟩

theorem exists_coefficient_gap_of_named_taylor_ne
    (U V : TaylorSlot → B) (p : B) (hp : p ≠ ⊥)
    (hne : p ≤ (taylorCodeName U =ᴮ taylorCodeName V)ᶜ)
    (hU : ∀ n b,ProperCutOn p (fun r => U (n,b,r)))
    (hV : ∀ n b,ProperCutOn p (fun r => V (n,b,r))) :
    ∃ (n : ℕ) (b : Bool) (q r : RatPresentation) (d : B),
      d ≠ ⊥ ∧ d ≤ p ∧ q.value < r.value ∧
        ((d ≤ U (n,b,r) ∧ d ≤ (V (n,b,q))ᶜ) ∨
         (d ≤ V (n,b,r) ∧ d ≤ (U (n,b,q))ᶜ)) := by
  classical
  obtain ⟨s,hs⟩ : ∃ s,p ⊓ U s ≠ p ⊓ V s := by
    by_contra! hAll
    exact hp (disjoint_compl_right.out _ (taylorCodeName_eq_of_mask hAll) hne)
  rcases s with ⟨n,b,q⟩
  obtain ⟨d,hd,hdp,hdOr⟩ := orient_boolean_mask_difference p _ _ hs
  rcases hdOr with h | h
  · have hCut : ProperCutOn d (fun r => U (n,b,r)) := by
      obtain ⟨a,c,e,f⟩ := hU n b
      exact ⟨hdp.trans a,hdp.trans c,fun r s hrs => (inf_le_inf_right _ hdp).trans (e r s hrs),
        fun r => (inf_le_inf_right _ hdp).trans (f r)⟩
    obtain ⟨r,m,hm,hmd,hqr,hr,hq⟩ :=
      strict_rational_gap_of_oriented_cut_bit (γ := fun s => V (n,b,s)) hCut hd h.1 h.2
    exact ⟨n,b,q,r,m,hm,hmd.trans hdp,hqr,Or.inl ⟨hr,hq⟩⟩
  · have hCut : ProperCutOn d (fun r => V (n,b,r)) := by
      obtain ⟨a,c,e,f⟩ := hV n b
      exact ⟨hdp.trans a,hdp.trans c,fun r s hrs => (inf_le_inf_right _ hdp).trans (e r s hrs),
        fun r => (inf_le_inf_right _ hdp).trans (f r)⟩
    obtain ⟨r,m,hm,hmd,hqr,hr,hq⟩ :=
      strict_rational_gap_of_oriented_cut_bit (γ := fun s => U (n,b,s)) hCut hd h.1 h.2
    exact ⟨n,b,q,r,m,hm,hmd.trans hdp,hqr,Or.inr ⟨hr,hq⟩⟩

end JSP000930.Positive
