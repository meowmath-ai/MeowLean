import JSP000930PositiveExplicitCutValidityNaturality

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem compl_eq_under_same_mask {p u v : B} (h : p ⊓ u = p ⊓ v) :
    p ⊓ uᶜ = p ⊓ vᶜ := by
  have hOne {a b : B} (h' : p ⊓ a = p ⊓ b) : p ⊓ aᶜ ≤ p ⊓ bᶜ := by
    apply le_inf inf_le_left
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have h₂ : (p ⊓ aᶜ) ⊓ b ≤ p ⊓ b := inf_le_inf inf_le_left le_rfl
    rw [← h'] at h₂
    exact (le_inf (h₂.trans inf_le_right) (inf_le_left.trans inf_le_right)).trans_eq
      inf_compl_eq_bot'
  exact le_antisymm (hOne h) (hOne h.symm)

theorem properCutOn_of_same_mask {p : B} {u v : RatPresentation → B}
    (h : ProperCutOn p u) (hm : ∀ q,p ⊓ u q = p ⊓ v q) : ProperCutOn p v := by
  have hmc (q : RatPresentation) : p ⊓ (u q)ᶜ = p ⊓ (v q)ᶜ :=
    compl_eq_under_same_mask (hm q)
  refine ⟨?_,?_,?_,?_⟩
  · have h₀ := le_inf (le_refl p) h.1
    rw [inf_iSup_eq] at h₀
    exact h₀.trans (iSup_le (fun q => (hm q).le.trans
      (inf_le_right.trans (le_iSup v q))))
  · have h₀ := le_inf (le_refl p) h.2.1
    rw [inf_iSup_eq] at h₀
    exact h₀.trans (iSup_le (fun q => (hmc q).le.trans
      (inf_le_right.trans (le_iSup (fun r => (v r)ᶜ) q))))
  · intro q r hqr
    calc
      p ⊓ v r = p ⊓ u r := (hm r).symm
      _ ≤ p ⊓ u q := le_inf inf_le_left (h.2.2.1 q r hqr)
      _ = p ⊓ v q := hm q
      _ ≤ v q := inf_le_right
  · intro q
    rw [← hm q]
    have hv := le_inf (show p ⊓ u q ≤ p from inf_le_left) (h.2.2.2 q)
    apply hv.trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro r
    rw [inf_iSup_eq]
    apply iSup_le
    intro hqr
    exact (hm r).le.trans (inf_le_right.trans
      (le_iSup_of_le r (le_iSup (fun _ : q.value < r.value => v r) hqr)))

end JSP000930.Positive
