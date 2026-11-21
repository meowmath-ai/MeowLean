import JSP000930RegularOpenPredensity

namespace JSP000930.Negative

open JSP000933.BooleanCompletion

universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem compatible_of_positive_analytic {p q : P} (v : RO P) (hv : v ≠ ⊥)
    (hp : v ≤ imageCondition p) (hq : v ≤ imageCondition q) : Compatible p q := by
  apply (compatible_iff_not_disjoint_r50 _ _).mpr
  intro h
  exact hv (le_bot_iff.mp ((le_inf hp hq).trans (disjoint_iff_inf_le.mp h)))

def JoinSide {I : Type u} (U : I → RO P) (p : P) : Prop :=
  (∃ i,p ∈ (U i : LowerSet P)) ∨ ∀ d ≤ p, ¬ ∃ i,d ∈ (U i : LowerSet P)

theorem dense_joinSide {I : Type u} (U : I → RO P) :
    DenseConditionSet {p | JoinSide U p} := by
  intro p
  classical
  by_cases h : ∃ d ≤ p,∃ i,d ∈ (U i : LowerSet P)
  · obtain ⟨d,hd,hi⟩ := h
    exact ⟨d,hd,Or.inl hi⟩
  · exact ⟨p,le_rfl,Or.inr (fun d hd hi => h ⟨d,hd,hi⟩)⟩

theorem old_inert_joinSide_incompatible {I : Type u} (U : I → RO P) (p d : P)
    (hp : p ∈ (((⨆ i,U i) : RO P) : LowerSet P)) (hd : ∀ r ≤ d,¬ ∃ i,r ∈ (U i : LowerSet P)) :
    ¬ Compatible p d := by
  intro h
  obtain ⟨r,hrp,hrd⟩ := h
  have hU (i : I) : imageCondition d ≤ (U i)ᶜ := by
    apply (JSP000933.ForcingTransport.image_le_iff_member d ((U i)ᶜ)).mpr
    change d ∈ ((U i : LowerSet P)ᶜ : LowerSet P)
    exact (mem_pseudoCompl_r50 _ d).mpr (fun t ht hti => hd t ht ⟨i,hti⟩)
  have hJoin : (⨆ i,U i) ≤ (imageCondition d)ᶜ := by
    apply iSup_le
    intro i
    simpa only [compl_compl] using compl_le_compl (hU i)
  exact imageCondition_ne_bot_r50 r (disjoint_compl_right.out _
    (imageCondition_mono_r50 hrd) ((imageCondition_mono_r50 hrp).trans
      (((JSP000933.ForcingTransport.image_le_iff_member p (⨆ i,U i)).mpr hp).trans hJoin)))

theorem basisImage_iSup (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q)
    {I : Type u} (U : I → RO P) :
    basisImage f (⨆ i,U i) = ⨆ i,basisImage f (U i) := by
  apply le_antisymm
  · let V := ⨆ i,basisImage f (U i)
    change basisImage f (⨆ i,U i) ≤ V
    apply iSup_le
    intro p
    by_contra h
    let T := imageCondition (f p.1) ⊓ Vᶜ
    have hT : T ≠ ⊥ := fun he =>
      h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨q,hq⟩ := imageCondition_dense_r50 T hT
    obtain ⟨d,hd,r,hrq,hrd⟩ := hf {p | JoinSide U p} (dense_joinSide U) q
    have hR : imageCondition r ≤ T := (imageCondition_mono_r50 hrq).trans hq
    have hRd := imageCondition_mono_r50 hrd
    have hCompat : Compatible p.1 d := hReflect (compatible_of_positive_analytic
      (imageCondition r) (imageCondition_ne_bot_r50 r) (hR.trans inf_le_left) hRd)
    rcases hd with hMember | hInert
    · obtain ⟨i,hi⟩ := hMember
      have hiV : imageCondition (f d) ≤ V :=
        (basisImage_of_member f (U i) hi).trans (le_iSup (fun j => basisImage f (U j)) i)
      exact imageCondition_ne_bot_r50 r (disjoint_compl_right.out _
        (hRd.trans hiV) (hR.trans inf_le_right))
    · exact old_inert_joinSide_incompatible U p.1 d p.2 hInert hCompat
  · apply iSup_le
    intro i
    exact basisImage_mono f (le_iSup U i)

end JSP000930.Negative
