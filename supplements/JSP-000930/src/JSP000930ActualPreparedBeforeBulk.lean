import JSP000930WetzelStageOrder

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

set_option maxHeartbeats 700000 in
theorem image_beforeBulk_eq_base (tail : WetzelTailPolicy)
    (p : BasedBefore tail wetzelBulkStage) :
    imageCondition p = (basedPrefixEmbed tail wetzel_bot_lt_bulk).toFun (baseMask tail p.val) := by
  let M := prefixMaskRealization tail wetzel_bot_lt_bulk
  apply le_antisymm
  · exact (M.image_le_iff p _).mpr le_rfl
  · apply le_of_image_tests
    intro q hq
    have hM : baseMask tail q.val ≤ baseMask tail p.val := (M.image_le_iff q _).mp hq
    apply (image_le_iff_member q _).mpr
    change q ∈ ((LowerSet.Iic p)ᶜᶜ : LowerSet (BasedBefore tail wetzelBulkStage))
    apply (mem_doublePseudoCompl_r50 _ q).mpr
    intro r hrq
    let b := baseMask tail r.val
    have hb : b ≠ ⊥ := baseMask_positive tail r.val
    let w : BasedBefore tail wetzelBulkStage :=
      ⟨putBase tail r.val b hb le_rfl,putBase_bounded tail wetzel_bot_lt_bulk r b hb le_rfl⟩
    have hwr : w ≤ r := putBase_le tail r.val b hb le_rfl
    refine ⟨w,hwr,?_⟩
    change w ≤ p
    intro i u hu
    have hi : i = ⊥ := before_wetzelBulk_only_base i (p.2 i ⟨u,hu⟩)
    subst i
    have huTop := ((basedPolicy_min_valid tail p.val.trace u).mp (p.val.valid _ u hu)).2
    have hpu : baseMask tail p.val = u.1 := by simp only [baseMask,hu,Option.getD_some]
    refine ⟨(b,⊤),?_,?_⟩
    · simp [w,putBase,attachTrace]
    · change b ≤ u.1 ∧ (⊤ : WetzelCertifiedLabel) ≤ u.2
      exact ⟨(baseMask_mono tail hrq).trans (hM.trans_eq hpu),by rw [huTop] <;> exact le_rfl⟩

theorem basedPrefixEmbed_beforeBulk_surjective (tail : WetzelTailPolicy) :
    Function.Surjective (basedPrefixEmbed tail wetzel_bot_lt_bulk).toFun := by
  intro U
  let F := basedPrefixEmbed tail wetzel_bot_lt_bulk
  let S := {p : BasedBefore tail wetzelBulkStage // p ∈ (U : LowerSet _)}
  let b : PreparedBA := ⨆ p : S,baseMask tail p.val.val
  refine ⟨b,?_⟩
  change F.toFun (⨆ p : S,baseMask tail p.val.val) = U
  rw [F.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [← image_beforeBulk_eq_base tail p.val]
    exact (image_le_iff_member p.val U).mpr p.2
  · apply le_of_image_tests
    intro p hp
    rw [image_beforeBulk_eq_base]
    exact le_iSup (fun q : S => F.toFun (baseMask tail q.val.val))
      ⟨p,(image_le_iff_member p U).mp hp⟩

noncomputable def actualBaseBeforeBulkIso (tail : WetzelTailPolicy) :
    PreparedBA ≃o RO (BasedBefore tail wetzelBulkStage) where
  toEquiv := Equiv.ofBijective (basedPrefixEmbed tail wetzel_bot_lt_bulk).toFun
    ⟨(basedPrefixEmbed tail wetzel_bot_lt_bulk).injective,basedPrefixEmbed_beforeBulk_surjective tail⟩
  map_rel_iff' := by
    intro a b
    let F := basedPrefixEmbed tail wetzel_bot_lt_bulk
    change F.toFun a ≤ F.toFun b ↔ a ≤ b
    exact ⟨F.reflect_le_r93, fun h => F.monotone h⟩

noncomputable def actualPreBulkModelIso (tail : WetzelTailPolicy) :
    PreparedBA ≃o PreStageAlgebra tail (a := wetzelBulkStage) :=
  (actualBaseBeforeBulkIso tail).trans
    (denseForcingMapOfIso930 (prefixOrderIso_r85 (basedPolicy tail) wetzelBulkStage)).pullIso.symm

end JSP000930.Negative
