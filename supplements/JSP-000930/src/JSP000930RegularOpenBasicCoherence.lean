import JSP000930RegularOpenCompleteMap

namespace JSP000930.Negative

open JSP000933.BooleanCompletion

universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem dense_below_or_incompatible (p : P) :
    DenseConditionSet {r | r ≤ p ∨ ¬ Compatible r p} := by
  intro r
  classical
  by_cases h : Compatible r p
  · obtain ⟨q,hqr,hqp⟩ := h
    exact ⟨q,hqr,Or.inl hqp⟩
  · exact ⟨r,le_rfl,Or.inr h⟩

theorem basisImage_imageCondition (f : P → Q) (hMono : Monotone f)
    (hf : PreservesPredensity f) (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q)
    (p : P) : basisImage f (imageCondition p) = imageCondition (f p) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    by_contra hx
    let T := imageCondition (f x.1) ⊓ (imageCondition (f p))ᶜ
    have hT : T ≠ ⊥ := fun he => hx (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨q,hq⟩ := imageCondition_dense_r50 T hT
    obtain ⟨d,hd,r,hrq,hrd⟩ := hf {r | r ≤ p ∨ ¬ Compatible r p}
      (dense_below_or_incompatible p) q
    have hR : imageCondition r ≤ T := (imageCondition_mono_r50 hrq).trans hq
    have hD := imageCondition_mono_r50 hrd
    rcases hd with hd|hd
    · exact imageCondition_ne_bot_r50 r (disjoint_compl_right.out _
        (hD.trans (imageCondition_mono_r50 (hMono hd))) (hR.trans inf_le_right))
    · obtain ⟨v,hvx,hvd⟩ := hReflect (compatible_of_positive_analytic
        (imageCondition r) (imageCondition_ne_bot_r50 r) (hR.trans inf_le_left) hD)
      have hMem : x.1 ∈ ((LowerSet.Iic p)ᶜᶜ : LowerSet P) := x.2
      obtain ⟨w,hw,hwp⟩ := (mem_doublePseudoCompl_r50 _ x.1).mp hMem v hvx
      exact hd ⟨w,hw.trans hvd,hwp⟩
  · exact basisImage_of_member f _ (imageCondition_mem_r50 p)

theorem completeMapFromPredensity_image (f : P → Q) (hMono : Monotone f)
    (hf : PreservesPredensity f) (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q)
    (p : P) : (completeMapFromPredensity f hf hReflect).toFun (imageCondition p) =
      imageCondition (f p) := basisImage_imageCondition f hMono hf hReflect p

end JSP000930.Negative
