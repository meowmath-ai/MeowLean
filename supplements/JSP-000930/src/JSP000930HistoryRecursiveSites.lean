import JSP000930ActualHistorySiteChoice

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion

noncomputable def actualHistorySites (a : GroundContinuumSuccIndex) : WetzelSiteRule a :=
  WellFounded.fix wellFounded_lt (fun i prev => actualHistorySiteStep i prev) a

theorem actualHistorySites_unfold (a : GroundContinuumSuccIndex) :
    actualHistorySites a =
      actualHistorySiteStep a (fun d _ => actualHistorySites d) :=
  WellFounded.fix_eq wellFounded_lt (fun i prev => actualHistorySiteStep i prev) a

theorem actualHistorySites_proper (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) : (actualHistorySites a old).CutOn ⊤ := by
  rw [actualHistorySites_unfold]
  exact actualHistorySiteStep_proper a _ old

theorem actualHistorySites_apart_capture (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (h : HistorySiteGuard a old) :
    ActualHistorySiteChoice a old h.1 (fun d _ => actualHistorySites d) (actualHistorySites a old) := by
  have he : actualHistorySites a old =
      actualHistorySiteStep a (fun d _ => actualHistorySites d) old :=
    congrFun (actualHistorySites_unfold a) old
  rw [he]
  exact actualHistorySiteStep_spec a _ old h

theorem actualHistorySites_in_native_prefix (rest : WetzelTailPolicy)
    (a : GroundContinuumSuccIndex)
    (h : BoundsSmallKappaNames (PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a))) :
    ActualHistorySiteChoice a (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a))
      (earlierHistory_persistent_r131 (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a))
      (fun d _ => actualHistorySites d)
      (actualHistorySites a
        (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a))) :=
  actualHistorySites_apart_capture a _
    ⟨earlierHistory_persistent_r131 _ _,nativeHistory_startsWithBulk rest a,h⟩

end JSP000930.Negative
