import JSP000933MarkedTraceRectangles

namespace JSP000933
namespace MarkedForcing

open BooleanCompletion

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem traceValue_pair_support_r430 (Q : ValuedPoset B N) (n k : N) :
    supportProjection Q (traceValue Q n⊓traceValue Q k)=commonRefinementValue Q n k := by
  let b := commonRefinementValue Q n k
  apply le_antisymm
  · apply (supportProjection_le_iff_r428 Q _ _).mpr
    by_contra hn
    have hN : (traceValue Q n⊓traceValue Q k)⊓(baseEmbed Q b)ᶜ≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
    have hPN : imageCondition p≤traceValue Q n := hp.trans (inf_le_left.trans inf_le_left)
    have hPK : imageCondition p≤traceValue Q k := hp.trans (inf_le_left.trans inf_le_right)
    have hPC : p.mask≤bᶜ := by
      apply (baseEmbed_reflects_mask_r427 p _).mp
      rw [baseEmbed_compl_r427]
      exact hp.trans inf_le_right
    obtain ⟨a,q,hqp,hQa⟩ := exists_stronger_below_indexedSup_r51 p
      (fun a : {a : TotalCondition Q // a.mask≤Q.refines a.trace n} => imageCondition a.val) hPN
    obtain ⟨d,s,hsq,hSd⟩ := exists_stronger_below_indexedSup_r51 q
      (fun d : {d : TotalCondition Q // d.mask≤Q.refines d.trace k} => imageCondition d.val)
      ((imageCondition_mono_r50 hqp).trans hPK)
    obtain ⟨t,hts,hta⟩ := exists_joint_of_image_le_r429
      ((imageCondition_mono_r50 hsq).trans hQa)
    obtain ⟨u,hut,hud⟩ := exists_joint_of_image_le_r429
      ((imageCondition_mono_r50 hts).trans hSd)
    have hua : u≤a.val := hut.trans hta
    have hup : u≤p := hut.trans (hts.trans (hsq.trans hqp))
    have huN : u.mask≤Q.refines u.trace n :=
      (le_inf hua.2 (hua.1.trans a.property)).trans (Q.trans _ _ _)
    have huK : u.mask≤Q.refines u.trace k :=
      (le_inf hud.2 (hud.1.trans d.property)).trans (Q.trans _ _ _)
    have huB : u.mask≤b := le_iSup_of_le u.trace (le_inf huN huK)
    exact u.nonzero (disjoint_compl_right.out _ huB (hup.1.trans hPC))
  · unfold commonRefinementValue
    apply iSup_le
    intro r
    let m := Q.refines r n⊓Q.refines r k
    by_cases hm : m=⊥
    · change m≤_
      rw [hm]
      exact bot_le
    · let p : TotalCondition Q :=
        ⟨m,r,hm,inf_le_left.trans ((Q.refine_valid r n).trans inf_le_left)⟩
      have h : imageCondition p≤traceValue Q n⊓traceValue Q k :=
        le_inf (image_le_traceValue_r429 p n inf_le_left) (image_le_traceValue_r429 p k inf_le_right)
      exact le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ traceValue Q n ⊓ traceValue Q k} => q.val.mask)
        ⟨p,h⟩

theorem projected_masked_pair_r430 (Q : ValuedPoset B N) (n k : N) (b : B) :
    supportProjection Q ((traceValue Q n⊓traceValue Q k)⊓baseEmbed Q b)=
      (commonRefinementValue Q n k)⊓b := by
  rw [supportProjection_meet_base_r428,traceValue_pair_support_r430]

theorem mask_forces_incompatibility_iff_r430 (Q : ValuedPoset B N) (n k : N) (b : B) :
    ((traceValue Q n⊓traceValue Q k)⊓baseEmbed Q b)=⊥ ↔
      Disjoint (commonRefinementValue Q n k) b := by
  rw [← supportProjection_zero_iff_r428 Q,projected_masked_pair_r430,disjoint_iff_inf_le,le_bot_iff]

end MarkedForcing
end JSP000933
