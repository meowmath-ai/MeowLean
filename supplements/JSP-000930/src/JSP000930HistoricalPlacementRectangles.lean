import JSP000930HistoricalNativeAdmission
import JSP000933RelativeTraceEnumeration

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing JSP000933.PreparedModel JSP000933.RelativeOCA

variable {P Q : Type} [Preorder P] [Preorder Q]

theorem orderIso_pull_imageCondition930 (e : P ≃o Q) (p : P) :
    (orderIsoDenseForcingMap e).pullIso (imageCondition (e p)) = imageCondition p := by
  apply le_antisymm
  · apply le_of_image_tests
    intro q hq
    apply (image_le_iff_member _ _).mpr
    have h := (image_le_iff_member _ _).mp hq
    change e q ∈ ((LowerSet.Iic (e p))ᶜᶜ : LowerSet Q) at h
    change q ∈ ((LowerSet.Iic p)ᶜᶜ : LowerSet P)
    apply (mem_doublePseudoCompl_r50 _ _).mpr
    intro r hr
    obtain ⟨s,hs,hsp⟩ := (mem_doublePseudoCompl_r50 _ _).mp h (e r) (e.monotone hr)
    exact ⟨e.symm s,(e.symm.monotone hs).trans_eq (e.symm_apply_apply r),
      (e.symm.monotone hsp).trans_eq (e.symm_apply_apply p)⟩
  · apply (image_le_iff_member _ _).mpr
    change e p ∈ (imageCondition (e p) : LowerSet Q)
    exact imageCondition_mem_r50 _

abbrev WetzelHistory (a : WetzelStageIndex) := StageHistory WetzelStageIndex PreparedBA WetzelMasterLabel a

noncomputable def historyBaseMask {a : WetzelStageIndex} {old : WetzelHistory a} (p : GoodPrefix old) :
    PreparedBA := ((p.trace ⊥).getD (⊤,⊤)).1

noncomputable def historyBaseCoefficient {a : WetzelStageIndex} (old : WetzelHistory a)
    (m : PreparedBA) : RO (GoodPrefix old) :=
  ⨆ p : {p : GoodPrefix old // historyBaseMask p ≤ m},imageCondition p.val

noncomputable def historyTraceCoefficient {a : WetzelStageIndex} (old : WetzelHistory a)
    (t : WetzelWholeTrace) : RO (GoodPrefix old) :=
  ⨆ p : {p : GoodPrefix old // stripBaseTrace p.trace = t.trace},imageCondition p.val

noncomputable def historyRectangle {a : WetzelStageIndex} (old : WetzelHistory a)
    (t : WetzelWholeTrace) (m : PreparedBA) : RO (GoodPrefix old) :=
  historyBaseCoefficient old m ⊓ historyTraceCoefficient old t

noncomputable def wetzelHistoryChart (rest : WetzelTailPolicy) (a : WetzelStageIndex) :
    RO (GoodPrefix (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) a)) ≃o
      RO (BasedBefore (wetzelBootstrapTail rest) a) :=
  (orderIsoDenseForcingMap (prefixOrderIso_r85 (basedPolicy (wetzelBootstrapTail rest)) a)).pullIso

theorem wetzelHistoryChart_baseCoefficient (rest : WetzelTailPolicy) {a : WetzelStageIndex}
    (ha : (⊥ : WetzelStageIndex)<a) (m : PreparedBA) :
    wetzelHistoryChart rest a
      (historyBaseCoefficient (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) a) m) =
      (prefixMaskRealization (wetzelBootstrapTail rest) ha).embed m := by
  let tail := wetzelBootstrapTail rest
  let e := prefixOrderIso_r85 (basedPolicy tail) a
  let E := wetzelHistoryChart rest a
  have he (p : BasedBefore tail a) : E (imageCondition (e p)) = imageCondition p :=
    orderIso_pull_imageCondition930 e p
  unfold historyBaseCoefficient
  change E (⨆ p : {p : GoodPrefix (earlierValidated (basedPolicy tail) a) // historyBaseMask p ≤ m},
    imageCondition p.val) = _
  rw [E.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro p
    let q := e.symm p.val
    have hq : e q=p.val := e.apply_symm_apply p.val
    rw [← hq,he,(prefixMaskRealization tail ha).image_le_iff]
    change historyBaseMask (e q) ≤ m
    rw [hq]
    exact p.property
  · apply le_of_image_tests
    intro p hp
    have h : historyBaseMask (e p) ≤ m :=
      ((prefixMaskRealization tail ha).image_le_iff p m).mp hp
    exact (he p).ge.trans (le_iSup (fun q : {p : GoodPrefix (earlierValidated (basedPolicy tail) a) //
      historyBaseMask p ≤ m} => E (imageCondition q.val)) ⟨e p,h⟩)

theorem wetzelHistoryChart_traceCoefficient (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (t : WetzelWholeTrace) (ht : TraceBelow wetzelScope a t) :
    wetzelHistoryChart rest (wetzelWorkStage a)
      (historyTraceCoefficient
        (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) t) =
      nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)
        (traceValue (nativeWetzelPrefixQ rest (wetzel_bot_lt_work a)) (wetzelEarlierTrace a t ht)) := by
  let tail := wetzelBootstrapTail rest
  let a' := wetzelWorkStage a
  let e := prefixOrderIso_r85 (basedPolicy tail) a'
  let E := wetzelHistoryChart rest a'
  let S := prefixTailPresentation tail (wetzel_bot_lt_work a)
  let n := wetzelEarlierTrace a t ht
  change E (⨆ p : {p : GoodPrefix (earlierValidated (basedPolicy tail) a') //
    stripBaseTrace p.trace = t.trace},imageCondition p.val) =
    S.denseMap.pullIso (traceValue S.quotient n)
  rw [E.map_iSup,S.pull_tail_traceValue]
  have he (p : BasedBefore tail a') : E (imageCondition (e p)) = imageCondition p :=
    orderIso_pull_imageCondition930 e p
  apply le_antisymm
  · apply iSup_le
    intro p
    let q := e.symm p.val
    have hq : e q=p.val := e.apply_symm_apply p.val
    have hs : S.strip q = n := by
      apply RawTail.extTrace
      change stripBaseTrace (e q).trace = t.trace
      simpa only [hq] using p.property
    rw [← hq,he]
    exact le_iSup (fun r : {p : BasedBefore tail a' // S.strip p = n} => imageCondition r.val) ⟨q,hs⟩
  · apply iSup_le
    intro p
    have hs : stripBaseTrace (e p.val).trace = t.trace :=
      congrArg RawTail.trace p.property
    exact (he p.val).ge.trans (le_iSup (fun q : {p : GoodPrefix (earlierValidated (basedPolicy tail) a') //
      stripBaseTrace p.trace = t.trace} => E (imageCondition q.val)) ⟨e p.val,hs⟩)

theorem wetzelHistoryChart_rectangle (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (t : WetzelWholeTrace) (ht : TraceBelow wetzelScope a t) (m : PreparedBA) :
    wetzelHistoryChart rest (wetzelWorkStage a)
      (historyRectangle
        (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) t m) =
      nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)
        (traceRectangle (nativeWetzelPrefixQ rest (wetzel_bot_lt_work a)) (wetzelEarlierTrace a t ht) m) := by
  unfold historyRectangle traceRectangle
  rw [OrderIso.map_inf,OrderIso.map_inf,wetzelHistoryChart_baseCoefficient,
    wetzelHistoryChart_traceCoefficient rest a t ht,nativeWetzelPrefixPull_base] <;> rfl

end JSP000930.Negative
