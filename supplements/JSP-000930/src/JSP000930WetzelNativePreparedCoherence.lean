import JSP000930NativeWetzelRelativePresentations

namespace JSP000930.Negative

open JSP000930.Positive.Cohen JSP000933.PreparedModel JSP000933.OpenGraphForcing
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing JSP000933.RelativeOCA

noncomputable def wetzelPrefixToPrefix (rest : WetzelTailPolicy) {a b : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (hab : a≤b) :
    CompleteValueMap (TotalBA (nativeWetzelPrefixQ rest ha))
      (TotalBA (nativeWetzelPrefixQ rest (ha.trans_le hab))) :=
  composeCompleteValueMaps
    (composeCompleteValueMaps (completeMapOfOrderIso930 (nativeWetzelPrefixPull rest ha))
      (prefixReduction hab).completeValueMap)
    (completeMapOfOrderIso930 (nativeWetzelPrefixPull rest (ha.trans_le hab)).symm)

theorem wetzelPrefixToPrefix_base (rest : WetzelTailPolicy) {a b : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (hab : a≤b) (x : PreparedBA) :
    (wetzelPrefixToPrefix rest ha hab).toFun (baseEmbed (nativeWetzelPrefixQ rest ha) x) =
      baseEmbed (nativeWetzelPrefixQ rest (ha.trans_le hab)) x := by
  let tail := wetzelBootstrapTail rest
  change (nativeWetzelPrefixPull rest (ha.trans_le hab)).symm
      ((prefixReduction hab).boolPullback
        (nativeWetzelPrefixPull rest ha (baseEmbed (nativeWetzelPrefixQ rest ha) x))) = _
  rw [nativeWetzelPrefixPull_base]
  change (nativeWetzelPrefixPull rest (ha.trans_le hab)).symm
      ((prefixReduction hab).boolPullback ((prefixMaskRealization tail ha).embed x)) = _
  rw [basedPrefix_base_commutes tail ha hab]
  change (nativeWetzelPrefixPull rest (ha.trans_le hab)).symm
    ((basedPrefixEmbed tail (ha.trans_le hab)).toFun x) = _
  rw [← nativeWetzelPrefixPull_base rest (ha.trans_le hab) x, OrderIso.symm_apply_apply]

theorem actualCommonCohen_to_finalWetzel_base (rest : WetzelTailPolicy) (x : PreparedBA) :
    (actualCommonCohen_to_finalWetzel rest).toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) x) =
      baseEmbed (nativeWetzelWholeQ rest) x := by
  let tail := wetzelBootstrapTail rest
  change (nativeWetzelWholePull rest).symm
    ((wholeReduction (R := iterationRules (basedPolicy tail)) (wetzelWorkStage firstGroundWetzelStage)).boolPullback
      ((actualWetzelCohen_toNative rest).toFun (baseEmbed (valuedCohen PreparedBA WetzelCoordinate) x))) = _
  rw [actualWetzelCohen_toNative_prepared]
  rw [basedWhole_base_commutes tail (wetzel_bot_lt_bulk.trans (wetzelBulk_lt_work firstGroundWetzelStage))]
  rw [← nativeWetzelWholePull_base,OrderIso.symm_apply_apply]

end JSP000930.Negative
