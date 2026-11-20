import JSP000933PreparedTypedDiamondDecoder
import JSP000933ActualReflectedProbes

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

variable (tail : BasedTailPolicy PreparedStage PreparedBA CliqueLabel)

noncomputable def typedPrefixROIso (a : PreparedStage) :
    PreStageAlgebra tail (a := a) ≃o RO (BasedBefore tail a) :=
  (orderIsoDenseForcingMap (prefixOrderIso_r85 (basedPolicy tail) a)).pullIso

theorem typedPrefixROIso_image (a : PreparedStage)
    (p : GoodPrefix (earlierValidated (basedPolicy tail) a)) :
    typedPrefixROIso tail a (imageCondition p) =
      imageCondition ((prefixOrderIso_r85 (basedPolicy tail) a).symm p) := by
  have h := DenseForcingMap.pull_imageMap
    (orderIsoDenseForcingMap (prefixOrderIso_r85 (basedPolicy tail) a))
    ((prefixOrderIso_r85 (basedPolicy tail) a).symm p)
  simpa [typedPrefixROIso,orderIsoDenseForcingMap] using h

theorem typedPreparedBase_image (a : PreparedStage) (ha : (⊥ : PreparedStage)<a) (b : PreparedBA) :
    typedPrefixROIso tail a (typedPreparedBase (earlierValidated (basedPolicy tail) a) b) =
      (prefixMaskRealization tail ha).embed b := by
  rw [typedPreparedBase,OrderIso.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [typedPrefixROIso_image]
    exact (prefixMaskRealization tail ha).image_le _ _ p.property
  · apply iSup_le
    intro p
    let iso := prefixOrderIso_r85 (basedPolicy tail) a
    have h : typedBaseMask (iso p.val)≤b := p.property
    apply le_iSup_of_le (⟨iso p.val,h⟩ : {p : GoodPrefix (earlierValidated (basedPolicy tail) a) //
        typedBaseMask p≤b})
    rw [typedPrefixROIso_image]
    change _ ≤ imageCondition (iso.symm (iso p.val))
    rw [iso.symm_apply_apply]

theorem typedRawTailJoin_image (a : PreparedStage) (ha : (⊥ : PreparedStage)<a)
    (n : PrefixTail a CliqueLabel) :
    typedPrefixROIso tail a (typedRawTailJoin (earlierValidated (basedPolicy tail) a)
        (includeRawTail (fun _ _ => trivial) n)) =
      (prefixTailPresentation tail ha).denseMap.pullIso
        (traceValue (prefixTailPresentation tail ha).quotient n) := by
  rw [typedRawTailJoin,OrderIso.map_iSup,(prefixTailPresentation tail ha).pull_tail_traceValue]
  let iso := prefixOrderIso_r85 (basedPolicy tail) a
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [typedPrefixROIso_image]
    have h : (prefixTailPresentation tail ha).strip (iso.symm p.val)=n :=
      RawTail.extTrace p.property
    exact le_iSup (fun q : {q : BasedBefore tail a //
      (prefixTailPresentation tail ha).strip q = n} => imageCondition q.val) ⟨iso.symm p.val,h⟩
  · apply iSup_le
    intro p
    have h : stripBaseTrace (iso p.val).trace =
        (includeRawTail (fun _ _ => trivial) n : WholeTail PreparedStage CliqueLabel).trace :=
      congrArg RawTail.trace p.property
    apply le_iSup_of_le (⟨iso p.val,h⟩ : {p : GoodPrefix (earlierValidated (basedPolicy tail) a) //
      stripBaseTrace p.trace = (includeRawTail (fun _ _ => trivial) n :
        WholeTail PreparedStage CliqueLabel).trace})
    rw [typedPrefixROIso_image]
    change _ ≤ imageCondition (iso.symm (iso p.val))
    rw [iso.symm_apply_apply]

noncomputable def typedToWhole (a : PreparedStage) :
    CompleteValueMap (PreStageAlgebra tail (a := a)) (RO (BasedCondition tail)) :=
  composeCompleteValueMaps (completeValueMapOfIso (typedPrefixROIso tail a))
    (wholeReduction (R := iterationRules (basedPolicy tail)) a).completeValueMap

theorem typedToWhole_base (a : PreparedStage) (ha : (⊥ : PreparedStage)<a) (b : PreparedBA) :
    (typedToWhole tail a).toFun (typedPreparedBase (earlierValidated (basedPolicy tail) a) b) =
      (wholeTailPresentation tail).denseMap.pullIso (baseEmbed (wholeTailPresentation tail).quotient b) := by
  change (wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
    (typedPrefixROIso tail a (typedPreparedBase (earlierValidated (basedPolicy tail) a) b)) = _
  rw [typedPreparedBase_image tail a ha]
  change (wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
    ((basedPrefixEmbed tail ha).toFun b) = _
  rw [basedWhole_base_commutes tail ha,(wholeTailPresentation tail).quotient_base_coherent]
  rfl

theorem typedToWhole_tail (a : PreparedStage) (ha : (⊥ : PreparedStage)<a)
    (n : WholeTail PreparedStage CliqueLabel) (hn : ∀ i,present n.trace i → i<a) :
    (typedToWhole tail a).toFun (typedRawTailJoin (earlierValidated (basedPolicy tail) a) n) =
      (wholeTailPresentation tail).denseMap.pullIso (traceValue (wholeTailPresentation tail).quotient n) := by
  let n' : PrefixTail a CliqueLabel := ⟨n.trace,n.finite,hn⟩
  have hEq : includeRawTail (fun _ _ => trivial) n'=n := RawTail.extTrace rfl
  rw [←hEq]
  change (wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
    (typedPrefixROIso tail a (typedRawTailJoin (earlierValidated (basedPolicy tail) a)
      (includeRawTail (fun _ _ => trivial) n'))) = _
  rw [typedRawTailJoin_image tail a ha,prefix_to_whole_traceValue tail ha]

theorem typedToWhole_probeRow (a : PreparedStage) (ha : (⊥ : PreparedStage)<a)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d i : GroundContinuumSuccIndex)
    (hF : ∀ j<d,∀ k,present (f j).trace k → k<a) :
    (typedToWhole tail a).toFun (typedProbeRow
      (earlierValidated (basedPolicy tail) a) f d i) =
      (wholeTailPresentation tail).denseMap.pullIso
        (guessedPrefixProbe (wholeTailPresentation tail).quotient f d i) := by
  rw [typedProbeRow,guessedPrefixProbe,(typedToWhole tail a).map_iSup,OrderIso.map_iSup]
  congr 1
  funext j
  rw [(typedToWhole tail a).map_inf,typedToWhole_base tail a ha,
    typedToWhole_tail tail a ha _ (hF j.val j.property)]
  let S := wholeTailPresentation tail
  let x := traceValue S.quotient (f j.val)
  let y := baseEmbed S.quotient (decodePreparedGuess d (kappaPairCode (i,j.val)))
  let e := S.denseMap.pullIso
  change e x ⊓ e y = e (y ⊓ x)
  exact (e.map_inf x y).symm.trans (congrArg e (inf_comm x y))

end ForcingTransport
end JSP000933
