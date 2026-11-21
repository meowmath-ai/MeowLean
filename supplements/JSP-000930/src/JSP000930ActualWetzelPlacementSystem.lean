import JSP000930WetzelNativePreparedCoherence
import JSP000933ExactNativeTraceCoherence
import JSP000930NegativePlacementPrefixReduction

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.FiniteSupport
open JSP000933.ForcingTransport JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA

def workPart : WetzelStageIndex → Option GroundContinuumSuccIndex
  | none => none
  | some none => none
  | some (some a) => some a

open scoped Classical in
noncomputable def wetzelScope (t : WetzelWholeTrace) : Finset GroundContinuumSuccIndex :=
  (t.scope.toList.filterMap workPart).toFinset

theorem wetzel_bot_lt_work (a : GroundContinuumSuccIndex) :
    (⊥ : WetzelStageIndex) < wetzelWorkStage a :=
  wetzel_bot_lt_bulk.trans (wetzelBulk_lt_work a)

theorem wetzelScope_support (t : WetzelWholeTrace) (a : GroundContinuumSuccIndex)
    (h : TraceBelow wetzelScope a t) :
    ∀ i,present t.trace i → i < wetzelWorkStage a := by
  classical
  intro i hi
  have hs : i ∈ t.scope := (RawTail.mem_scope t i).mpr hi
  cases i with
  | none => exact wetzel_bot_lt_work a
  | some i =>
    cases i with
    | bot => exact wetzelBulk_lt_work a
    | coe i =>
      have hi : i ∈ wetzelScope t := List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨wetzelWorkStage i,Finset.mem_toList.mpr hs,rfl⟩)
      exact (wetzelWorkStage_lt_iff _ _).mpr (h i hi)

def wetzelEarlierTrace (a : GroundContinuumSuccIndex) (t : WetzelWholeTrace)
    (h : TraceBelow wetzelScope a t) : PrefixTail (wetzelWorkStage a) WetzelCertifiedLabel :=
  ⟨t.trace,t.finite,wetzelScope_support t a h⟩

noncomputable def wetzelPrefixToWhole (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (h : (⊥ : WetzelStageIndex)<a) :
    CompleteValueMap (TotalBA (nativeWetzelPrefixQ rest h)) (TotalBA (nativeWetzelWholeQ rest)) :=
  composeCompleteValueMaps
    (composeCompleteValueMaps (completeMapOfOrderIso930 (nativeWetzelPrefixPull rest h))
      (wholeReduction (R := iterationRules (basedPolicy (wetzelBootstrapTail rest))) a).completeValueMap)
    (completeMapOfOrderIso930 (nativeWetzelWholePull rest).symm)

theorem wetzelPrefixToWhole_trace (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (n : PrefixTail a WetzelCertifiedLabel) :
    (wetzelPrefixToWhole rest ha).toFun (traceValue (nativeWetzelPrefixQ rest ha) n) =
      traceValue (nativeWetzelWholeQ rest) (includeRawTail (fun _ _ => trivial) n) := by
  apply (nativeWetzelWholePull rest).injective
  change (nativeWetzelWholePull rest) ((nativeWetzelWholePull rest).symm _) = _
  rw [OrderIso.apply_symm_apply]
  exact prefix_to_whole_traceValue (wetzelBootstrapTail rest) ha n

theorem wetzelPrefixToWhole_base (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (b : PreparedBA) :
    (wetzelPrefixToWhole rest ha).toFun (baseEmbed (nativeWetzelPrefixQ rest ha) b) =
      baseEmbed (nativeWetzelWholeQ rest) b := by
  let tail := wetzelBootstrapTail rest
  change (nativeWetzelWholePull rest).symm
    ((wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
      (nativeWetzelPrefixPull rest ha (baseEmbed (nativeWetzelPrefixQ rest ha) b))) = _
  rw [nativeWetzelPrefixPull_base,basedWhole_base_commutes tail ha,← nativeWetzelWholePull_base,
    OrderIso.symm_apply_apply]

noncomputable def nativeWetzelPlacementSystem (rest : WetzelTailPolicy) :
    PlacementPrefixSystem (nativeWetzelWholeQ rest) where
  scope := wetzelScope
  Trace a := PrefixTail (wetzelWorkStage a) WetzelCertifiedLabel
  poset a := nativeWetzelPrefixQ rest (wetzel_bot_lt_work a)
  into a := wetzelPrefixToWhole rest (wetzel_bot_lt_work a)
  earlierTrace := wetzelEarlierTrace
  rectangle := by
    intro a t ht b
    have hT : includeRawTail (fun _ _ => trivial) (wetzelEarlierTrace a t ht) = t :=
      RawTail.extTrace rfl
    simp only [traceRectangle,(wetzelPrefixToWhole rest (wetzel_bot_lt_work a)).map_inf,
      wetzelPrefixToWhole_base,wetzelPrefixToWhole_trace,hT]

end JSP000930.Negative
