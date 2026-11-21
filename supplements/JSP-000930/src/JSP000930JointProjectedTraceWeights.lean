import JSP000930MarkedForcingPairOps
import JSP000933MarkedNameTransport

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport

variable {B N : Type} [NontrivialCompleteBooleanAlgebra B]

theorem traceWeights_joint_support (P : ValuedPoset B N)
    (x y : TotalBA P) (n k : N) (b : B) :
    ((traceWeight P x n ⊓ traceWeight P y k) ⊓ commonRefinementValue P n k) ⊓ b ≤
      supportProjection P ((x ⊓ y) ⊓ baseEmbed P b) := by
  unfold traceWeight commonRefinementValue
  rw [iSup_inf_iSup,iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  rintro ⟨⟨u,v⟩,r⟩
  let m := ((u.val.mask ⊓ v.val.mask) ⊓ (P.refines r n ⊓ P.refines r k)) ⊓ b
  change m ≤ _
  by_cases hm : m = ⊥
  · simpa only [hm] using
      (bot_le : (⊥ : B) ≤ supportProjection P ((x ⊓ y) ⊓ baseEmbed P b))
  have hu : m ≤ P.refines r u.val.trace := by
    rw [u.property.1]
    exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hv : m ≤ P.refines r v.val.trace := by
    rw [v.property.1]
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  let q : TotalCondition P := ⟨m,r,hm,hu.trans ((P.refine_valid _ _).trans inf_le_left)⟩
  have hqu : q ≤ u.val :=
    ⟨inf_le_left.trans (inf_le_left.trans inf_le_left),hu⟩
  have hqv : q ≤ v.val :=
    ⟨inf_le_left.trans (inf_le_left.trans inf_le_right),hv⟩
  have hxQ := (imageCondition_mono_r50 hqu).trans u.property.2
  have hyQ := (imageCondition_mono_r50 hqv).trans v.property.2
  have hbQ := image_le_baseEmbed_r427 q b inf_le_right
  exact (supportProjection_image_r428 P q).symm.le.trans
    (supportProjection_mono_r428 P (le_inf (le_inf hxQ hyQ) hbQ))

theorem supportProjection_iSup930 (P : ValuedPoset B N)
    {I : Type} (U : I → TotalBA P) :
    supportProjection P (⨆ i,U i) = ⨆ i,supportProjection P (U i) := by
  apply le_antisymm
  · apply (supportProjection_le_iff_r428 _ _ _).mpr
    rw [baseEmbed_joins_r427]
    exact iSup_le fun i => le_iSup_of_le i
      ((supportProjection_le_iff_r428 _ _ _).mp le_rfl)
  · exact iSup_le fun i => supportProjection_mono_r428 P (le_iSup U i)

end JSP000930.Negative
