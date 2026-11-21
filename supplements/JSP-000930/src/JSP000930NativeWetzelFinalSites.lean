import JSP000930NativeHistorySiteCoherence
import JSP000930NegativeLiteralFinalContinuum

open bSet Cardinal
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion

theorem boundsKappa_ofOrderIso930 {B C : Type} [CompleteBooleanAlgebra B]
    [CompleteBooleanAlgebra C] (e : B ≃o C) (hB : BoundsSmallKappaNames B) :
    BoundsSmallKappaNames C := by
  intro I hI V
  have h := e.monotone (hB I hI (fun i j => e.symm (V i j)))
  simpa only [e.map_iInf,e.map_iSup,e.apply_symm_apply] using h

theorem nativeWetzelPrefix_boundsKappa (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (h : ProjectedAntichainCCC (prefixMaskRealization (wetzelBootstrapTail rest)
      (wetzel_bot_lt_work a)).project) :
    BoundsSmallKappaNames (PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)) :=
  boundsKappa_ofOrderIso930
    ((nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)).trans
      (wetzelHistoryChart rest (wetzelWorkStage a)).symm)
    (prepared_relativeCCC_boundsKappa (nativeWetzelPrefixQ_relativeCCC rest (wetzel_bot_lt_work a) h))

theorem mapComplexBits_eqTruth930 {B C : Type} [NontrivialCompleteBooleanAlgebra B]
    [NontrivialCompleteBooleanAlgebra C] (F : CompleteValueMap B C) (x y : ComplexBits B) :
    ((mapComplexBits F x).name =ᴮ (mapComplexBits F y).name) =
      F.toFun (x.name =ᴮ y.name) := by
  rw [← liftName_complexSite F x,← liftName_complexSite F y]
  exact (coefficientsOfValueMap F).liftName_eq x.name y.name

noncomputable def nativeWetzelFinalSite (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex) :
    ComplexBits (JSP000933.MarkedForcing.TotalBA (nativeWetzelWholeQ rest)) :=
  mapComplexBits (wetzelHistoryToWhole rest a)
    (actualHistorySites a
      (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)))

theorem nativeWetzelFinalSite_proper (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex) :
    (nativeWetzelFinalSite rest a).CutOn ⊤ := by
  have h := properSite_map (wetzelHistoryToWhole rest a) (actualHistorySites a _)
    (actualHistorySites_proper a _)
  rwa [(wetzelHistoryToWhole rest a).map_top] at h

theorem nativeWetzelFinalSite_eq_earlier (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (i : {d : GroundContinuumSuccIndex // d<a}) :
    let P := basedPolicy (wetzelBootstrapTail rest)
    let old := earlierValidated P (wetzelWorkStage a)
    mapComplexBits (wetzelHistoryToWhole rest a)
      (earlierWetzelSiteInHistory a old (earlierHistory_persistent_r131 P _)
        (fun d _ => actualHistorySites d) i) = nativeWetzelFinalSite rest i.val := by
  dsimp only
  let P := basedPolicy (wetzelBootstrapTail rest)
  let old := earlierValidated P (wetzelWorkStage a)
  let s := actualHistorySites i.val (earlierValidated P (wetzelWorkStage i.val))
  let F := wetzelHistoryToWhole rest a
  let H := historyCompleteEmbed ((wetzelWorkStage_le_iff _ _).mpr i.property.le)
    old (earlierHistory_persistent_r131 P _)
  change ComplexBits.mk (fun q => F.toFun (H.toFun (s.re q))) (fun q => F.toFun (H.toFun (s.im q))) =
    ComplexBits.mk (fun q => (wetzelHistoryToWhole rest i.val).toFun (s.re q))
      (fun q => (wetzelHistoryToWhole rest i.val).toFun (s.im q))
  exact congrArg₂ ComplexBits.mk
    (funext fun q => wetzelHistoryToWhole_commutes rest i.property.le (s.re q))
    (funext fun q => wetzelHistoryToWhole_commutes rest i.property.le (s.im q))

theorem nativeWetzelFinalSite_apart_of_lt (rest : WetzelTailPolicy) {a b : GroundContinuumSuccIndex}
    (hab : a<b)
    (hB : BoundsSmallKappaNames (PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage b))) :
    ((nativeWetzelFinalSite rest b).name =ᴮ (nativeWetzelFinalSite rest a).name) = ⊥ := by
  let P := basedPolicy (wetzelBootstrapTail rest)
  let F := wetzelHistoryToWhole rest b
  let old := earlierValidated P (wetzelWorkStage b)
  let i : {i : GroundContinuumSuccIndex // i<b} := ⟨a,hab⟩
  have h := (actualHistorySites_in_native_prefix rest b hB).2.1 i
  have he := nativeWetzelFinalSite_eq_earlier rest b i
  change mapComplexBits F
    (earlierWetzelSiteInHistory b old (earlierHistory_persistent_r131 P _) (fun d _ => actualHistorySites d) i) =
    nativeWetzelFinalSite rest a at he
  rw [← he]
  change ((mapComplexBits F (actualHistorySites b old)).name =ᴮ
    (mapComplexBits F (earlierWetzelSiteInHistory b old (earlierHistory_persistent_r131 P _)
      (fun d _ => actualHistorySites d) i)).name) = ⊥
  rw [mapComplexBits_eqTruth930,h,F.map_bot]

end JSP000930.Negative
