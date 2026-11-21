import JSP000930NativeWorkingProjectedCCC
import JSP000933PreparedPrefixCHRealCodes

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.PreparedModel JSP000933.MarkedForcing JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport
open JSP000933.FiniteSupport

theorem beforeBulk_projectedCCC (tail : WetzelTailPolicy) :
    ProjectedAntichainCCC (prefixMaskRealization tail wetzel_bot_lt_bulk).project := by
  let M := prefixMaskRealization tail wetzel_bot_lt_bulk
  let E := actualBaseBeforeBulkIso tail
  have hM (x : RO (BasedBefore tail wetzelBulkStage)) : M.project x = E.symm x := by
    have h (b : PreparedBA) : M.project x ≤ b ↔ E.symm x ≤ b := by
      rw [M.project_gc]
      change x ≤ E b ↔ E.symm x ≤ b
      rw [← E.le_iff_le,E.apply_symm_apply]
    exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)
  intro v hv
  have hDisj (i j : OmegaOneIndex) (hij : i<j) : Disjoint (E.symm (v i)) (E.symm (v j)) := by
    apply disjoint_iff_inf_le.mpr
    rw [← E.symm.map_inf,← E.symm.map_bot]
    exact E.symm.monotone (disjoint_iff_inf_le.mp (hv i j hij))
  change unboundedValue (fun i => M.project (v i)) = ⊥
  simp only [hM]
  apply le_bot_iff.mp
  apply (unboundedValue_le_pairOverlap_r431 _).trans
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  exact disjoint_iff_inf_le.mp (hDisj i j.1 j.2)

theorem actualBulkPrefix_projectedCCC (rest : WetzelTailPolicy) :
    ProjectedAntichainCCC (prefixMaskRealization (wetzelBootstrapTail rest)
      (wetzel_bot_lt_bulk.trans (wetzelBulk_lt_work firstGroundWetzelStage))).project := by
  let tail := wetzelBootstrapTail rest
  let Q := wetzelTaggedBulk (B := PreStageAlgebra tail (a := wetzelBulkStage))
  have hv : TailStageValues tail (a := wetzelBulkStage) = CertifiedStageLabel.admits Q :=
    wetzelBootstrapTail_bulk rest _
  have hMono : Monotone (TailStageValues tail (a := wetzelBulkStage)) :=
    hv.symm ▸ CertifiedStageLabel.admits_mono Q
  have ht : TailStageValues tail (a := wetzelBulkStage) ⊤ = ⊤ := by rw [hv,CertifiedStageLabel.admits_top]
  have hB : BoundsCountableOmegaOneNames (PreStageAlgebra tail (a := wetzelBulkStage)) :=
    rowBounds_ofIso (actualPreBulkModelIso tail) prepared_boundsOmegaOne_r432
  apply basedPrefix_successor_projectedCCC tail wetzel_bot_lt_bulk hMono ht wetzelBulk_next
    (beforeBulk_projectedCCC tail)
  rw [nativeTailValuePoset_eq_certified tail Q hMono ht hv]
  exact relativeCCC_certified Q (wetzelTaggedBulk_relativeCCC hB)

theorem actualBulkPrefix_preserves_omegaOne (rest : WetzelTailPolicy) :
    BoundsCountableOmegaOneNames
      (RO (BasedBefore (wetzelBootstrapTail rest) (wetzelWorkStage firstGroundWetzelStage))) := by
  apply rowBounds_ofIso (nativeWetzelBulkComparison rest).pullIso
  exact relativeCCC_preserves_boundsOmegaOne_r436 (valuedCohen PreparedBA WetzelCoordinate)
    prepared_boundsOmegaOne_r432 (cohen_forcesRelativeCCC prepared_boundsOmegaOne_r432)

end JSP000930.Negative
