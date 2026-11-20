import JSP000933MarkedProjection

namespace JSP000933
namespace MarkedForcing

open BooleanCompletion

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem exists_joint_of_image_le_r429 {P : Type*} [Preorder P] {p q : P}
    (h : imageCondition p≤ imageCondition q) : Compatible p q := by
  apply (compatible_iff_not_disjoint_r50 _ _).mpr
  intro hd
  exact imageCondition_ne_bot_r50 p (hd.out _ le_rfl h)

theorem baseEmbed_meets_r429 (Q : ValuedPoset B N) (a b : B) :
    baseEmbed Q (a⊓b)=baseEmbed Q a⊓baseEmbed Q b := by
  apply le_antisymm
  · exact le_inf (baseEmbed_mono_r427 Q inf_le_left) (baseEmbed_mono_r427 Q inf_le_right)
  · by_contra hn
    have hd : (baseEmbed Q a⊓baseEmbed Q b)⊓(baseEmbed Q (a⊓b))ᶜ≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hd
    have ha := (baseEmbed_reflects_mask_r427 p a).mp (hp.trans (inf_le_left.trans inf_le_left))
    have hb := (baseEmbed_reflects_mask_r427 p b).mp (hp.trans (inf_le_left.trans inf_le_right))
    exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _
      (image_le_baseEmbed_r427 p (a⊓b) (le_inf ha hb)) (hp.trans inf_le_right))

noncomputable def traceValue (Q : ValuedPoset B N) (n : N) : TotalBA Q :=
  ⨆ p : {p : TotalCondition Q // p.mask≤Q.refines p.trace n},imageCondition p.val

theorem image_le_traceValue_r429 {Q : ValuedPoset B N} (p : TotalCondition Q) (n : N)
    (h : p.mask≤Q.refines p.trace n) : imageCondition p≤traceValue Q n :=
  le_iSup (fun q : {q : TotalCondition Q // q.mask ≤ Q.refines q.trace n} => imageCondition q.val) ⟨p,h⟩

theorem traceValue_support_r429 (Q : ValuedPoset B N) (n : N) :
    supportProjection Q (traceValue Q n)=Q.valid n := by
  apply le_antisymm
  · apply (supportProjection_le_iff_r428 Q _ _).mpr
    apply iSup_le
    intro p
    exact image_le_baseEmbed_r427 p.val _ (p.property.trans ((Q.refine_valid _ _).trans inf_le_right))
  · by_cases hn : Q.valid n=⊥
    · rw [hn]
      exact bot_le
    · let p : TotalCondition Q := ⟨Q.valid n,n,hn,le_rfl⟩
      have h := supportProjection_mono_r428 Q (image_le_traceValue_r429 p n (Q.refl n))
      rw [supportProjection_image_r428] at h
      exact h

theorem image_eq_base_meet_trace_r429 {Q : ValuedPoset B N} (p : TotalCondition Q) :
    imageCondition p=baseEmbed Q p.mask⊓traceValue Q p.trace := by
  apply le_antisymm
  · exact le_inf (image_le_baseEmbed_r427 p _ le_rfl)
      (image_le_traceValue_r429 p _ (p.valid.trans (Q.refl _)))
  · rw [traceValue,inf_iSup_eq]
    apply iSup_le
    intro q
    by_contra hn
    have hN : (baseEmbed Q p.mask⊓imageCondition q.val)⊓(imageCondition p)ᶜ≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨s,hs⟩ := imageCondition_dense_r50 _ hN
    obtain ⟨r,hrs,hrq⟩ := exists_joint_of_image_le_r429 (hs.trans (inf_le_left.trans inf_le_right))
    have hm : r.mask≤p.mask :=
      hrs.1.trans ((baseEmbed_reflects_mask_r427 s p.mask).mp
        (hs.trans (inf_le_left.trans inf_le_left)))
    have hRef : r.mask≤Q.refines r.trace p.trace :=
      (le_inf hrq.2 (hrq.1.trans q.property)).trans (Q.trans _ _ _)
    exact imageCondition_ne_bot_r50 r (disjoint_compl_right.out _
      (imageCondition_mono_r50 (show r≤p from ⟨hm,hRef⟩))
      ((imageCondition_mono_r50 hrs).trans (hs.trans inf_le_right)))

end MarkedForcing
end JSP000933
