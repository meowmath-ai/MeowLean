import JSP000930ActualWetzelBulkStage

namespace JSP000930.Negative

open JSP000930.Positive.Cohen JSP000933.PreparedModel JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.MarkedForcing
open JSP000933.FiniteSupport

variable {A B N M P : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
variable [NontrivialCompleteBooleanAlgebra B] [Preorder P]

theorem castDenseMap_mask930 (Q R : ValuedPoset B N) (h : Q = R)
    (D : DenseForcingMap P (TotalCondition Q)) (p : P) :
    ((h ▸ D : DenseForcingMap P (TotalCondition R)).map p).mask = (D.map p).mask := by
  cases h
  rfl

theorem nativeCertifiedSuccessor_mask
    (tail : BasedTailPolicy A B (CertifiedStageLabel N)) {a b : A} (ha : a ≠ ⊥)
    (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (PreStageAlgebra tail (a := a)) N)
    (hA : TailStageValues tail (a := a) = CertifiedStageLabel.admits Q)
    (p : BasedBefore tail b) :
    ((nativeCertifiedSuccessor tail ha succ Q hA).map p).mask =
      imageCondition (typedRestrict (basedPolicy tail) p.val a) := by
  unfold nativeCertifiedSuccessor
  change ((nativeTailValuePoset_eq_certified tail Q _ _ hA ▸
    markedSuccessorComparison tail ha _ _ succ : DenseForcingMap (BasedBefore tail b)
      (TotalCondition (certifiedQ Q))).map p).mask = _
  rw [castDenseMap_mask930]
  rfl

theorem nativeWetzelBulkComparison_mask (rest : WetzelTailPolicy)
    (p : BasedBefore (wetzelBootstrapTail rest) (wetzelWorkStage firstGroundWetzelStage)) :
    ((nativeWetzelBulkComparison rest).map p).mask =
      (actualPreBulkModelIso (wetzelBootstrapTail rest)).symm
        (imageCondition (typedRestrict (basedPolicy (wetzelBootstrapTail rest)) p.val wetzelBulkStage)) := by
  let tail := wetzelBootstrapTail rest
  let Q := wetzelTaggedBulk (B := PreStageAlgebra tail (a := wetzelBulkStage))
  have hA : TailStageValues tail (a := wetzelBulkStage) = CertifiedStageLabel.admits Q :=
    wetzelBootstrapTail_bulk rest _
  exact congrArg (actualPreBulkModelIso tail).symm
    (nativeCertifiedSuccessor_mask tail wetzelBulkStage_ne_bot wetzelBulk_next Q hA p)

theorem actualWetzelCohen_toNative_prepared (rest : WetzelTailPolicy) (b : PreparedBA) :
    (actualWetzelCohen_toNative rest).toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) b) =
      (basedPrefixEmbed (wetzelBootstrapTail rest)
        (wetzel_bot_lt_bulk.trans (wetzelBulk_lt_work firstGroundWetzelStage))).toFun b := by
  let tail := wetzelBootstrapTail rest
  let h := wetzel_bot_lt_bulk.trans (wetzelBulk_lt_work firstGroundWetzelStage)
  let Q := valuedCohen PreparedBA WetzelCoordinate
  let D := nativeWetzelBulkComparison rest
  change D.pullIso (baseEmbed Q b) = (basedPrefixEmbed tail h).toFun b
  have htest (p : BasedBefore tail (wetzelWorkStage firstGroundWetzelStage)) :
      imageCondition p ≤ D.pullIso (baseEmbed Q b) ↔
      imageCondition p ≤ (basedPrefixEmbed tail h).toFun b := by
    rw [image_le_iff_member]
    change D.map p ∈ (baseEmbed Q b : LowerSet (TotalCondition Q)) ↔
      imageCondition p ≤ (basedPrefixEmbed tail h).toFun b
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427]
    change ((nativeWetzelBulkComparison rest).map p).mask ≤ b ↔
      imageCondition p ≤ (prefixMaskRealization tail h).embed b
    rw [(prefixMaskRealization tail h).image_le_iff,nativeWetzelBulkComparison_mask rest p]
    let E := denseForcingMapOfIso930 (prefixOrderIso_r85 (basedPolicy tail) wetzelBulkStage)
    let p₀ := restrict p.val wetzelBulkStage
    have hE : E.pullIso (imageCondition (typedRestrict (basedPolicy tail) p.val wetzelBulkStage)) =
        imageCondition p₀ := by
      apply le_antisymm
      · apply le_of_image_tests
        intro q hq
        apply (image_le_iff_member _ _).mpr
        have hh := (image_le_iff_member _ _).mp hq
        change E.map q ∈ (imageCondition (E.map p₀) : LowerSet _) at hh
        change q ∈ ((LowerSet.Iic p₀)ᶜᶜ : LowerSet _)
        apply (mem_doublePseudoCompl_r50 _ _).mpr
        intro r hr
        have hrE := E.monotone hr
        have hhE : E.map q ∈ ((LowerSet.Iic (E.map p₀))ᶜᶜ : LowerSet _) := hh
        obtain ⟨s,hs,hsp⟩ := (mem_doublePseudoCompl_r50 _ _).mp hhE _ hrE
        let e := prefixOrderIso_r85 (basedPolicy tail) wetzelBulkStage
        have hs' : s ≤ e r := hs
        have hsp' : s ≤ e p₀ := hsp
        exact ⟨e.symm s,(e.symm.monotone hs').trans_eq (e.symm_apply_apply r),
          (e.symm.monotone hsp').trans_eq (e.symm_apply_apply p₀)⟩
      · apply (image_le_iff_member _ _).mpr
        change E.map p₀ ∈ (imageCondition (E.map p₀) : LowerSet _)
        exact imageCondition_mem_r50 _
    change (actualBaseBeforeBulkIso tail).symm
        (E.pullIso (imageCondition (typedRestrict (basedPolicy tail) p.val wetzelBulkStage))) ≤ b ↔
      baseMask tail p.val ≤ b
    rw [hE,image_beforeBulk_eq_base]
    change (actualBaseBeforeBulkIso tail).symm ((actualBaseBeforeBulkIso tail)
      (baseMask tail p₀.val)) ≤ b ↔ _
    rw [(actualBaseBeforeBulkIso tail).symm_apply_apply,baseMask_restrict tail _ wetzel_bot_lt_bulk]
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

end JSP000930.Negative
