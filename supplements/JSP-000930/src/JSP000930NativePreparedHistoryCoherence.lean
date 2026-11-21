import JSP000930ActualNativeWorkingPolicy

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

theorem wetzelHistoryPreparedMap_comp {a j : GroundContinuumSuccIndex} (hja : j≤a)
    (old : WetzelHistory (wetzelWorkStage a)) (hP : HistoryPersistent old)
    (hInit : HistoryStartsWithBulk (a := a) old) (u : PreparedBA) :
    let h := (wetzelWorkStage_le_iff _ _).mpr hja
    (historyCompleteEmbed h old hP).toFun
      ((wetzelHistoryPreparedMap j (subHistory h old) (subHistory_persistent h old hP)
        (historyStartsWithBulk_sub hja old hInit)).toFun u) =
      (wetzelHistoryPreparedMap a old hP hInit).toFun u := by
  let h := (wetzelWorkStage_le_iff _ _).mpr hja
  let h₀ := (wetzelWorkStage_le_iff _ _).mpr (firstGroundWetzelStage_le j)
  let x : RO (GoodPrefix (subHistory (h₀.trans h) old)) :=
    ((orderIsoReduction (goodPrefixCongr930 hInit)).completeValueMap).toFun
      (checkedBulkToHistory.toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) u))
  change (historyCompleteEmbed h old hP).toFun
      ((historyCompleteEmbed h₀ (subHistory h old) (subHistory_persistent h old hP)).toFun x) =
        (historyCompleteEmbed (h₀.trans h) old hP).toFun x
  exact historyCompleteEmbed_comp_exact h₀ h old hP x

noncomputable def actualPreparedAt (a : GroundContinuumSuccIndex) :
    CompleteValueMap PreparedBA (ActualWorkBA a) :=
  wetzelHistoryPreparedMap a (ActualWorkOld a)
    (earlierHistory_persistent_r131 actualWetzelPolicy _)
    (nativeHistory_startsWithBulk actualWetzelRest a)

noncomputable def actualHistoryShift {a b : GroundContinuumSuccIndex} (hab : a≤b) :
    CompleteValueMap (ActualWorkBA a) (ActualWorkBA b) :=
  historyCompleteEmbed ((wetzelWorkStage_le_iff _ _).mpr hab) (ActualWorkOld b)
    (earlierHistory_persistent_r131 actualWetzelPolicy _)

theorem actualHistoryShift_prepared {a b : GroundContinuumSuccIndex} (hab : a≤b) (u : PreparedBA) :
    (actualHistoryShift hab).toFun ((actualPreparedAt a).toFun u) =
      (actualPreparedAt b).toFun u :=
  wetzelHistoryPreparedMap_comp hab (ActualWorkOld b)
    (earlierHistory_persistent_r131 actualWetzelPolicy _) (nativeHistory_startsWithBulk actualWetzelRest b) u

end JSP000930.Negative
