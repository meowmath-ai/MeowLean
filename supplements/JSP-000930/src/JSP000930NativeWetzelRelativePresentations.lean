import JSP000930FiniteMasterTailCardinality
import JSP000933RawTailCCCAndTraceJoins

namespace JSP000930.Negative

open JSP000930.Positive.Cohen JSP000933.PreparedModel JSP000933.OpenGraphForcing
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing JSP000933.RelativeOCA

abbrev WetzelWholeTrace := WholeTail WetzelStageIndex WetzelCertifiedLabel

noncomputable def nativeWetzelWholeQ (rest : WetzelTailPolicy) : ValuedPoset PreparedBA WetzelWholeTrace :=
  (wholeTailPresentation (wetzelBootstrapTail rest)).quotient

noncomputable def nativeWetzelPrefixQ (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) :
    ValuedPoset PreparedBA (PrefixTail a WetzelCertifiedLabel) :=
  (prefixTailPresentation (wetzelBootstrapTail rest) ha).quotient

noncomputable def nativeWetzelWholePull (rest : WetzelTailPolicy) :
    TotalBA (nativeWetzelWholeQ rest) ≃o RO (BasedCondition (wetzelBootstrapTail rest)) :=
  (wholeTailPresentation (wetzelBootstrapTail rest)).denseMap.pullIso

noncomputable def nativeWetzelPrefixPull (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) :
    TotalBA (nativeWetzelPrefixQ rest ha) ≃o RO (BasedBefore (wetzelBootstrapTail rest) a) :=
  (prefixTailPresentation (wetzelBootstrapTail rest) ha).denseMap.pullIso

theorem nativeWetzelWholePull_base (rest : WetzelTailPolicy) (b : PreparedBA) :
    nativeWetzelWholePull rest (baseEmbed (nativeWetzelWholeQ rest) b) =
      (basedBaseEmbed (wetzelBootstrapTail rest)).toFun b :=
  (wholeTailPresentation (wetzelBootstrapTail rest)).quotient_base_coherent b

theorem nativeWetzelPrefixPull_base (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (b : PreparedBA) :
    nativeWetzelPrefixPull rest ha (baseEmbed (nativeWetzelPrefixQ rest ha) b) =
      (basedPrefixEmbed (wetzelBootstrapTail rest) ha).toFun b :=
  (prefixTailPresentation (wetzelBootstrapTail rest) ha).quotient_base_coherent b

noncomputable def actualCommonCohen_to_finalWetzel (rest : WetzelTailPolicy) :
    CompleteValueMap WetzelCohenBA (TotalBA (nativeWetzelWholeQ rest)) :=
  composeCompleteValueMaps
    (composeCompleteValueMaps (actualWetzelCohen_toNative rest)
      (wholeReduction (R := iterationRules (basedPolicy (wetzelBootstrapTail rest)))
        (wetzelWorkStage firstGroundWetzelStage)).completeValueMap)
    (completeMapOfOrderIso930 (nativeWetzelWholePull rest).symm)

theorem nativeWetzelWholeQ_relativeCCC (rest : WetzelTailPolicy)
    (h : ProjectedAntichainCCC (basedMaskRealization (wetzelBootstrapTail rest)).project) :
    ForcesRelativeCCC (nativeWetzelWholeQ rest) :=
  (wholeTailPresentation (wetzelBootstrapTail rest)).quotient_relativeCCC h

theorem nativeWetzelPrefixQ_relativeCCC (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a)
    (h : ProjectedAntichainCCC (prefixMaskRealization (wetzelBootstrapTail rest) ha).project) :
    ForcesRelativeCCC (nativeWetzelPrefixQ rest ha) :=
  (prefixTailPresentation (wetzelBootstrapTail rest) ha).quotient_relativeCCC h

end JSP000930.Negative
