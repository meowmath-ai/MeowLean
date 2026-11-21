import JSP000930RelativeCCCOrderIsoTransport

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

noncomputable def createdCohenIsoToHistory (a : GroundContinuumSuccIndex) :
    ActualWorkCohenBA a ≃o ActualWorkBA (wetzelGroundNext a) := by
  let D : DenseForcingMap (GoodPrefix (ActualWorkOld (wetzelGroundNext a)))
      (TotalCondition ((actualWorkingInputs a).stage a)) :=
    historicalStageComparison (ActualWorkOld (wetzelGroundNext a)) (actual_work_lt_successor a)
      (earlierHistory_persistent_r131 actualWetzelPolicy _) (wetzelWork_next a)
      ((actualWorkingInputs a).stage a)
      (nativeWetzel_pastAdmitted (wetzelGroundNext a) ((wetzelGroundNext_spec a a).mpr le_rfl))
  exact ((actualWorkingInputs a).comparison a).pullIso.trans D.pullIso

theorem createdCohenIsoToHistory_apply (a : GroundContinuumSuccIndex) (x : ActualWorkCohenBA a) :
    createdCohenIsoToHistory a x = (createdCohenToHistory a).toFun x := rfl

theorem createdCohenToHistory_base (a : GroundContinuumSuccIndex) (x : ActualWorkBA a) :
    (createdCohenToHistory a).toFun (((actualWorkingInputs a).oldToCohen a).toFun x) =
      (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le).toFun x :=
  historicalWorkCohenEmbed_base ((wetzelGroundNext_spec a a).mpr le_rfl)
    (earlierHistory_persistent_r131 actualWetzelPolicy _) (actualWorkingInputs a)
    (nativeWetzel_pastAdmitted (wetzelGroundNext a) ((wetzelGroundNext_spec a a).mpr le_rfl))
    (wetzelWork_next a) x

theorem actualRelativeCCC_after_work_oldBase (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex)
    (hPrev : ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project)
    (hA : ForcesRelativeCCC ((actualWorkingInputs a).row a))
    (hJ : ForcesRelativeCCC (valuedPair ((actualWorkingInputs a).row a) (actualSurvivorProduct a s))) :
    ForcesRelativeCCC (changeValuedBase
      (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le) (actualSurvivorProduct a s)) := by
  let W := actualWorkingInputs a
  let P := W.row a
  let R := actualSurvivorProduct a s
  let F := W.oldToCohen a
  let G := completeMapOfOrderIso930 (createdCohenIsoToHistory a)
  have hC : ForcesRelativeCCC (changeValuedBase F R) :=
    relativeCCC_survivor_after_actual_work (X := WorkCohenCoordinate)
      (actualWorkingPrefix_boundsOmegaOne a hPrev) P R hA hJ
  have hD := relativeCCC_changeOrderIso930 (createdCohenIsoToHistory a) (changeValuedBase F R) hC
  change ForcesRelativeCCC (changeValuedBase G (changeValuedBase F R)) at hD
  rw [changeValuedBase_comp_exact] at hD
  have he :
      (composeCompleteValueMaps F G).toFun =
        (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le).toFun := by
    funext x
    change createdCohenIsoToHistory a (F.toFun x) = _
    rw [createdCohenIsoToHistory_apply]
    exact createdCohenToHistory_base a x
  rwa [changeValuedBase_congr930 _ _ he] at hD

end JSP000930.Negative
