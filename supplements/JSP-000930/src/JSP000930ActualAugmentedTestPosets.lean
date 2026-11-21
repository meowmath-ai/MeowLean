import JSP000930ExactNativeWetzelTraceMaps

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

noncomputable def actualPrefixHistoryIso (a : GroundContinuumSuccIndex) :
    ActualWorkBA a ≃o TotalBA (actualPrefixQ a) :=
  (wetzelHistoryChart actualWetzelRest (wetzelWorkStage a)).trans
    (nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work a)).symm

theorem actualPrefixHistoryIso_apply (a : GroundContinuumSuccIndex) (x : ActualWorkBA a) :
    actualPrefixHistoryIso a x = (wetzelHistoryToPrefix actualWetzelRest a).toFun x := rfl

theorem actualPrefixHistoryIso_shift {a b : GroundContinuumSuccIndex} (hab : a≤b) (x : ActualWorkBA a) :
    (actualPrefixQuotientShift hab).toFun (actualPrefixHistoryIso a x) =
      actualPrefixHistoryIso b ((actualHistoryShift hab).toFun x) := by
  let E := nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work b)
  let D := nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work a)
  let h := (wetzelWorkStage_le_iff _ _).mpr hab
  apply E.injective
  change E (E.symm ((prefixReduction h).boolPullback
    (D (D.symm (wetzelHistoryChart actualWetzelRest (wetzelWorkStage a) x))))) =
    E (E.symm (wetzelHistoryChart actualWetzelRest (wetzelWorkStage b) ((actualHistoryShift hab).toFun x)))
  rw [E.apply_symm_apply,D.apply_symm_apply,E.apply_symm_apply]
  exact (wetzelHistoryChart_map_between actualWetzelRest hab x).symm

abbrev ActualSurvivorLabels (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :=
  (↥s : Type) → SupportedSymbolic GroundContinuumSuccIndex (WorkingDomain a)

noncomputable def normalizedSurvivorQ (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :
    ValuedPoset (TotalBA (actualPrefixQ a)) (ActualSurvivorLabels a s) :=
  changeValuedBase (completeMapOfOrderIso930 (actualPrefixHistoryIso a)) (actualSurvivorProduct a s)

noncomputable def actualAugmentedQ (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :=
  augmentedQ (actualPrefixQ a) (normalizedSurvivorQ a s)

theorem normalizedSurvivorQ_ccc_iff (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :
    ForcesRelativeCCC (normalizedSurvivorQ a s) ↔ ForcesRelativeCCC (actualSurvivorProduct a s) := by
  let e := actualPrefixHistoryIso a
  let P := actualSurvivorProduct a s
  let Q := normalizedSurvivorQ a s
  constructor
  · intro h
    have hc := relativeCCC_changeOrderIso930 e.symm Q h
    change ForcesRelativeCCC (changeValuedBase (completeMapOfOrderIso930 e.symm)
      (changeValuedBase (completeMapOfOrderIso930 e) P)) at hc
    rw [changeValuedBase_comp_exact] at hc
    have hE : changeValuedBase (composeCompleteValueMaps (completeMapOfOrderIso930 e)
        (completeMapOfOrderIso930 e.symm)) P = P := by
      apply valuedPoset_ext_values
      · funext p
        exact e.symm_apply_apply (P.valid p)
      · funext p q
        exact e.symm_apply_apply (P.refines p q)
      · rfl
    rwa [hE] at hc
  · exact relativeCCC_changeOrderIso930 e P

theorem actualAugmentedQ_of_stageCCC (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex)
    (hP : ActualWetzelPrefixCCC a) (hS : ForcesRelativeCCC (actualSurvivorProduct a s)) :
    ForcesRelativeCCC (actualAugmentedQ a s) :=
  actualAugmented_relativeCCC_of_inner930 (actualPrefixQ a) (normalizedSurvivorQ a s)
    (nativeWetzelPrefixQ_relativeCCC actualWetzelRest _ hP)
    ((normalizedSurvivorQ_ccc_iff a s).mpr hS)

theorem actualSurvivorProduct_of_augmentedCCC (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (h : ForcesRelativeCCC (actualAugmentedQ a s)) :
    ForcesRelativeCCC (actualSurvivorProduct a s) :=
  (normalizedSurvivorQ_ccc_iff a s).mp
    (actualAugmented_innerCCC_of_relative930 (actualPrefixQ a) (normalizedSurvivorQ a s) h)

def actualSurvivorLabelInclude {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : ActualSurvivorLabels a s) : ActualSurvivorLabels b s :=
  fun r => includeSymbolicSupport (fun _ h => h.trans_le hab) (p r)

theorem actualSurvivor_valid_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : ActualSurvivorLabels a s) :
    (actualPrefixQuotientShift hab).toFun ((normalizedSurvivorQ a s).valid p) =
      (normalizedSurvivorQ b s).valid (actualSurvivorLabelInclude hab s p) := by
  let H := actualHistoryShift hab
  let F := actualPrefixQuotientShift hab
  let E := actualPrefixHistoryIso b
  change F.toFun (actualPrefixHistoryIso a (⨅ r : s,(actualSurvivorRow a r.val).valid (p r))) =
    E (⨅ r : s,(actualSurvivorRow b r.val).valid (actualSurvivorLabelInclude hab s p r))
  rw [actualPrefixHistoryIso_shift,H.map_iInf]
  congr 1
  apply iInf_congr
  intro r
  exact symbolicLabel_partial_map H _ _ _ _
    (fun j hj => actualWorkingSite_transport hab hj)
    (fun j hj n => actualWetzelRowPalette_transport hab hj r.val n) (p r).val (p r).2

theorem actualSurvivor_refines_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p q : ActualSurvivorLabels a s) :
    (actualPrefixQuotientShift hab).toFun ((normalizedSurvivorQ a s).refines p q) =
      (normalizedSurvivorQ b s).refines (actualSurvivorLabelInclude hab s p) (actualSurvivorLabelInclude hab s q) := by
  let H := actualHistoryShift hab
  let F := actualPrefixQuotientShift hab
  let E := actualPrefixHistoryIso b
  change F.toFun (actualPrefixHistoryIso a (⨅ r : s,(actualSurvivorRow a r.val).refines (p r) (q r))) =
    E (⨅ r : s,(actualSurvivorRow b r.val).refines (actualSurvivorLabelInclude hab s p r)
      (actualSurvivorLabelInclude hab s q r))
  rw [actualPrefixHistoryIso_shift,H.map_iInf]
  congr 1
  apply iInf_congr
  intro r
  exact symbolicLabel_refines_partial_map H _ _ _ _
    (fun j hj => actualWorkingSite_transport hab hj)
    (fun j hj n => actualWetzelRowPalette_transport hab hj r.val n)
      (p r).val (q r).val (p r).2 (q r).2

end JSP000930.Negative
