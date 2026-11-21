import JSP000930NegativeInertOutsideAndGlue

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem unboundedValue_eq_bot_of_disjoint (w : OmegaOneIndex → B)
    (h : ∀ i j,i < j → Disjoint (w i) (w j)) :
    unboundedValue w = ⊥ := by
  let x := unboundedValue w
  apply le_bot_iff.mp
  have hx (i : OmegaOneIndex) :
      x ≤ ⨆ j : {j : OmegaOneIndex // i < j},w j.val := iInf_le _ i
  have hn : Nonempty OmegaOneIndex := Cardinal.mk_ne_zero_iff.mp (by
    rw [mk_OmegaOneIndex_r61]
    exact (Cardinal.aleph_pos _).ne')
  obtain ⟨i₀⟩ := hn
  have hFull : x ≤ ⨆ j,w j :=
    (hx i₀).trans (iSup_le fun j => le_iSup w j.val)
  calc
    x = x ⊓ (⨆ j,w j) := (inf_eq_left.mpr hFull).symm
    _ = ⨆ i,x ⊓ w i := inf_iSup_eq _ _
    _ ≤ ⊥ := by
      apply iSup_le
      intro i
      apply (inf_le_inf_right _ (hx i)).trans
      rw [iSup_inf_eq]
      exact iSup_le fun j => disjoint_iff_inf_le.mp (h i j.val j.property).symm

theorem inertOutside_relativeCCC_iff (Q : ValuedPoset B N) (m : B) :
    ForcesRelativeCCC (inertOutside Q m) ↔ RelativeCCCOn Q m := by
  constructor
  · intro hc W hV hSep
    let V (i : OmegaOneIndex) (t : N) := m ⊓ W i t
    have hValid (i : OmegaOneIndex) (t : N) :
        V i t ≤ (inertOutside Q m).valid t :=
      (inf_le_inf_left m (hV i t)).trans le_sup_left
    have hValidSep (i j : OmegaOneIndex) (hij : i < j) (t u : N) :
        (V i t ⊓ V j u) ⊓ commonRefinementValue (inertOutside Q m) t u = ⊥ := by
      apply le_bot_iff.mp
      have hh : V i t ⊓ V j u ≤ m := inf_le_left.trans inf_le_left
      have hk : (V i t ⊓ V j u) ⊓ commonRefinementValue (inertOutside Q m) t u ≤
          m ⊓ commonRefinementValue (inertOutside Q m) t u :=
        le_inf (inf_le_left.trans hh) inf_le_right
      have hC : m ⊓ commonRefinementValue (inertOutside Q m) t u =
          m ⊓ commonRefinementValue Q t u := by
        rw [inertOutside_common,inertOutside_clip]
      exact (le_inf (inf_le_left.trans
        (inf_le_inf (show V i t ≤ W i t from inf_le_right)
          (show V j u ≤ W j u from inf_le_right))) (hk.trans (hC.le.trans inf_le_right))).trans_eq (hSep i j hij t u)
    have h := hc V hValid hValidSep
    simpa only [V,← inf_iSup_eq,unboundedValue_inf_mask] using h
  · intro hc W hV hSep
    let V (i : OmegaOneIndex) (t : N) := m ⊓ W i t
    have hValid (i : OmegaOneIndex) (t : N) : V i t ≤ Q.valid t := by
      have h := inf_le_inf_left m (hV i t)
      change V i t ≤ m ⊓ inertOutsideValue m (Q.valid t) at h
      rw [inertOutside_clip] at h
      exact h.trans inf_le_right
    have hVSep (i j : OmegaOneIndex) (hij : i < j) (t u : N) :
        (V i t ⊓ V j u) ⊓ commonRefinementValue Q t u = ⊥ := by
      apply le_bot_iff.mp
      have h₀ : (V i t ⊓ V j u) ⊓ commonRefinementValue Q t u ≤
          m ⊓ commonRefinementValue Q t u :=
        le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right
      rw [← inertOutside_clip m (commonRefinementValue Q t u),← inertOutside_common] at h₀
      exact (le_inf (inf_le_left.trans
        (inf_le_inf (show V i t ≤ W i t from inf_le_right)
          (show V j u ≤ W j u from inf_le_right))) (h₀.trans inf_le_right)).trans_eq (hSep i j hij t u)
    let v (i : OmegaOneIndex) := ⨆ t,W i t
    let x := unboundedValue v
    have hIn : m ⊓ x = ⊥ := by
      have h : m ⊓ unboundedValue (fun i => ⨆ t,V i t) = ⊥ := hc V hValid hVSep
      simpa only [V,← inf_iSup_eq,unboundedValue_inf_mask,← inf_assoc,inf_idem,v,x] using h
    have hOut : mᶜ ⊓ x = ⊥ := by
      rw [← unboundedValue_inf_mask]
      apply unboundedValue_eq_bot_of_disjoint
      intro i j hij
      apply disjoint_iff_inf_le.mpr
      simp only [v,inf_iSup_eq]
      apply iSup_le
      intro u
      rw [iSup_inf_eq]
      apply iSup_le
      intro t
      have he : (mᶜ ⊓ W i t) ⊓ (mᶜ ⊓ W j u) ≤ mᶜ :=
        inf_le_left.trans inf_le_left
      have hc : mᶜ ≤ commonRefinementValue (inertOutside Q m) t u := by
        rw [inertOutside_common]
        exact le_sup_right
      exact (le_inf (inf_le_inf inf_le_right inf_le_right) (he.trans hc)).trans_eq
        (hSep i j hij t u)
    change x = ⊥
    rw [← top_inf_eq x,← (sup_compl_eq_top (x := m)),inf_sup_right,hIn,hOut,sup_bot_eq]

end JSP000930.Negative
