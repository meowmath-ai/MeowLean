import JSP000930NativePreparedHistoryCoherence

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

theorem goodPrefixCongr_baseCoefficient930 {a : WetzelStageIndex}
    {old h : WetzelHistory a} (e : old=h) (u : PreparedBA) :
    (orderIsoReduction (goodPrefixCongr930 e)).boolPullback (historyBaseCoefficient h u) =
      historyBaseCoefficient old u := by
  cases e
  have ht (p : GoodPrefix old) :
      imageCondition p ≤ (orderIsoReduction (goodPrefixCongr930 (rfl : old=old))).boolPullback
        (historyBaseCoefficient old u) ↔ imageCondition p ≤ historyBaseCoefficient old u := by
    rw [image_le_regular_pullback] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
    (le_of_image_tests (fun p => (ht p).mpr))

theorem checkedBulkToHistory_base (u : PreparedBA) :
    checkedBulkToHistory.toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) u) =
      historyBaseCoefficient WetzelBulkHistory u := by
  let a := wetzelWorkStage firstGroundWetzelStage
  let E := wetzelHistoryChart idleWetzelTail a
  apply E.injective
  change E (E.symm ((actualWetzelCohen_toNative idleWetzelTail).toFun
    (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) u))) = _
  rw [E.apply_symm_apply,actualWetzelCohen_toNative_prepared]
  exact (wetzelHistoryChart_baseCoefficient idleWetzelTail (wetzel_bot_lt_work firstGroundWetzelStage) u).symm

theorem actualPreparedAt_is_baseCoefficient (a : GroundContinuumSuccIndex) (u : PreparedBA) :
    (actualPreparedAt a).toFun u = historyBaseCoefficient (ActualWorkOld a) u := by
  let f := firstGroundWetzelStage
  let h := (wetzelWorkStage_le_iff _ _).mpr (firstGroundWetzelStage_le a)
  let old := ActualWorkOld a
  let hP := earlierHistory_persistent_r131 actualWetzelPolicy (wetzelWorkStage a)
  let hInit := nativeHistory_startsWithBulk actualWetzelRest a
  change (historyCompleteEmbed h old hP).toFun
    ((orderIsoReduction (goodPrefixCongr930 hInit)).boolPullback
      (checkedBulkToHistory.toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) u))) = _
  rw [checkedBulkToHistory_base]
  apply (congrArg (historyCompleteEmbed h old hP).toFun (goodPrefixCongr_baseCoefficient930 hInit u)).trans
  apply (wetzelHistoryChart actualWetzelRest (wetzelWorkStage a)).injective
  apply (wetzelHistoryChart_map_between actualWetzelRest (firstGroundWetzelStage_le a)
    (historyBaseCoefficient (ActualWorkOld f) u)).trans
  rw [wetzelHistoryChart_baseCoefficient actualWetzelRest (wetzel_bot_lt_work f)]
  rw [basedPrefix_base_commutes actualWetzelTail (wetzel_bot_lt_work f) h]
  exact (wetzelHistoryChart_baseCoefficient actualWetzelRest (wetzel_bot_lt_work a) u).symm

theorem actualPreparedAt_as_native_mask (a : GroundContinuumSuccIndex) (u : PreparedBA) :
    (wetzelHistoryToPrefix actualWetzelRest a).toFun ((actualPreparedAt a).toFun u) =
      baseEmbed (nativeWetzelPrefixQ actualWetzelRest (wetzel_bot_lt_work a)) u := by
  let D := nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work a)
  apply D.injective
  rw [actualPreparedAt_is_baseCoefficient]
  change D (D.symm (wetzelHistoryChart actualWetzelRest (wetzelWorkStage a)
    (historyBaseCoefficient (ActualWorkOld a) u))) = _
  rw [D.apply_symm_apply,wetzelHistoryChart_baseCoefficient]
  exact (nativeWetzelPrefixPull_base actualWetzelRest (wetzel_bot_lt_work a) u).symm

end JSP000930.Negative
