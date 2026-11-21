import JSP000930ActualPreparedBeforeBulk

namespace JSP000930.Negative

open JSP000930.Positive.Cohen JSP000933.PreparedModel JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.MarkedForcing

variable {B C X : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def cohenOrderIsoOfBase (e : B ≃o C) (X : Type) :
    TotalCondition (valuedCohen B X) ≃o TotalCondition (valuedCohen C X) where
  toFun p := ⟨e p.mask,p.trace,fun h => p.nonzero (e.injective (h.trans e.map_bot.symm)),le_top⟩
  invFun p := ⟨e.symm p.mask,p.trace,
    fun h => p.nonzero (e.symm.injective (h.trans e.symm.map_bot.symm)),le_top⟩
  left_inv p := totalCondition_eq_of_data _ _ (e.symm_apply_apply p.mask) rfl
  right_inv p := totalCondition_eq_of_data _ _ (e.apply_symm_apply p.mask) rfl
  map_rel_iff' := by
    intro p q
    rw [cohen_total_le_iff,cohen_total_le_iff]
    exact ⟨fun h => ⟨e.le_iff_le.mp h.1,h.2⟩,fun h => ⟨e.monotone h.1,h.2⟩⟩

noncomputable def nativeWetzelBulkComparison (rest : WetzelTailPolicy) :
    DenseForcingMap (BasedBefore (wetzelBootstrapTail rest) (wetzelWorkStage firstGroundWetzelStage))
      (TotalCondition (valuedCohen PreparedBA WetzelCoordinate)) := by
  let tail := wetzelBootstrapTail rest
  let D := nativeCertifiedSuccessor tail wetzelBulkStage_ne_bot wetzelBulk_next
    (wetzelTaggedBulk (B := PreStageAlgebra tail (a := wetzelBulkStage)))
    (wetzelBootstrapTail_bulk rest _)
  let T := wetzelBulkTagDense (B := PreStageAlgebra tail (a := wetzelBulkStage))
  let F := denseForcingMapOfIso930
    (cohenOrderIsoOfBase (actualPreBulkModelIso tail).symm WetzelCoordinate)
  exact denseForcingMap_comp930 (denseForcingMap_comp930 D T) F

noncomputable def actualWetzelCohen_toNative (rest : WetzelTailPolicy) :
    CompleteValueMap WetzelCohenBA
      (RO (BasedBefore (wetzelBootstrapTail rest) (wetzelWorkStage firstGroundWetzelStage))) :=
  completeMapOfDensePull930 (nativeWetzelBulkComparison rest)

end JSP000930.Negative
