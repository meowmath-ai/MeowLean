import JSP000933MarkedBaseEmbedding

namespace JSP000933
namespace MarkedForcing

open BooleanCompletion

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def supportProjection (Q : ValuedPoset B N) (x : TotalBA Q) : B :=
  ⨆ p : {p : TotalCondition Q // imageCondition p≤x},p.val.mask

theorem supportProjection_le_iff_r428 (Q : ValuedPoset B N) (x : TotalBA Q) (b : B) :
    supportProjection Q x≤b ↔ x≤baseEmbed Q b := by
  constructor
  · intro h
    by_contra hn
    have hk : x⊓(baseEmbed Q b)ᶜ≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hk
    have hPB : p.mask≤b := (le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ x} => q.val.mask)
      ⟨p,hp.trans inf_le_left⟩).trans h
    exact imageCondition_ne_bot_r50 p
      (disjoint_compl_right.out _ (image_le_baseEmbed_r427 p b hPB) (hp.trans inf_le_right))
  · intro h
    apply iSup_le
    intro p
    exact (baseEmbed_reflects_mask_r427 p.val b).mp (p.property.trans h)

theorem supportProjection_gc_r428 (Q : ValuedPoset B N) :
    GaloisConnection (supportProjection Q) (baseEmbed Q) :=
  supportProjection_le_iff_r428 Q

theorem supportProjection_mono_r428 (Q : ValuedPoset B N) :
    Monotone (supportProjection Q) := by
  intro x y h
  apply iSup_le
  intro p
  exact le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ y} => q.val.mask)
    ⟨p.val,p.property.trans h⟩

theorem baseEmbed_reflects_r428 (Q : ValuedPoset B N) {a b : B} :
    baseEmbed Q a≤baseEmbed Q b ↔ a≤b := by
  constructor
  · intro h
    by_cases ha : a=⊥
    · rw [ha]
      exact bot_le
    · let p := weakenToBase Q a ha
      exact (baseEmbed_reflects_mask_r427 p b).mp ((image_le_baseEmbed_r427 p a le_rfl).trans h)
  · intro h
    exact baseEmbed_mono_r427 Q h

theorem supportProjection_image_r428 (Q : ValuedPoset B N) (p : TotalCondition Q) :
    supportProjection Q (imageCondition p)=p.mask := by
  apply le_antisymm
  · exact (supportProjection_le_iff_r428 Q _ _).mpr (image_le_baseEmbed_r427 p p.mask le_rfl)
  · exact le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ imageCondition p} => q.val.mask)
      ⟨p,le_rfl⟩

theorem supportProjection_meet_base_r428 (Q : ValuedPoset B N) (x : TotalBA Q) (b : B) :
    supportProjection Q (x⊓baseEmbed Q b)=(supportProjection Q x)⊓b := by
  apply le_antisymm
  · exact le_inf (supportProjection_mono_r428 Q inf_le_left)
      ((supportProjection_le_iff_r428 Q _ _).mpr inf_le_right)
  · unfold supportProjection
    rw [iSup_inf_eq]
    apply iSup_le
    intro p
    by_cases hp : p.val.mask⊓b=⊥
    · rw [hp]
      exact bot_le
    · let q := intersectMask p.val b hp
      have hqx : imageCondition q≤x :=
        (imageCondition_mono_r50 (intersectMask_le_r426 p.val b hp)).trans p.property
      have hqb : imageCondition q≤baseEmbed Q b := image_le_baseEmbed_r427 q b inf_le_right
      exact le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ x ⊓ baseEmbed Q b} => q.val.mask)
        ⟨q,le_inf hqx hqb⟩

theorem supportProjection_zero_iff_r428 (Q : ValuedPoset B N) (x : TotalBA Q) :
    supportProjection Q x=⊥ ↔ x=⊥ := by
  simp only [← le_bot_iff, supportProjection_le_iff_r428,baseEmbed_bot_r427]

noncomputable def forcedByBase (Q : ValuedPoset B N) (x : TotalBA Q) : B :=
  (supportProjection Q xᶜ)ᶜ

theorem baseEmbed_le_iff_forced_r428 (Q : ValuedPoset B N) (x : TotalBA Q) (b : B) :
    baseEmbed Q b≤x ↔ b≤forcedByBase Q x := by
  constructor
  · intro h
    have hC : xᶜ≤baseEmbed Q bᶜ := by
      rw [baseEmbed_compl_r427]
      exact compl_le_compl h
    have hp := (supportProjection_le_iff_r428 Q _ _).mpr hC
    simpa only [forcedByBase,compl_compl] using compl_le_compl hp
  · intro h
    have hp : supportProjection Q xᶜ≤bᶜ := by
      simpa only [forcedByBase,compl_compl] using compl_le_compl h
    have hC := (supportProjection_le_iff_r428 Q _ _).mp hp
    rw [baseEmbed_compl_r427] at hC
    simpa only [compl_compl] using compl_le_compl hC

end MarkedForcing
end JSP000933
