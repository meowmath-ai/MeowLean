import JSP000930NativeWetzelFinalSites

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing

theorem nativeWetzelFinalSite_captures_trial (rest : WetzelTailPolicy)
    (hB : ∀ a : GroundContinuumSuccIndex,
      BoundsSmallKappaNames (PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)))
    (i : PlacementTrialIndex) :
    let z := fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i
    trialValidity z ≤ ⨆ j : GroundContinuumSuccIndex,z.name =ᴮ (nativeWetzelFinalSite rest j).name := by
  obtain ⟨a,_,hpick,hReady0⟩ := wetzelTrial_ready_cofinally i firstGroundWetzelStage
  have hReady : fixedWetzelPlacementBook.TrialReady wetzelScope a (wetzelTrialPick a) := by
    rwa [hpick]
  let P := basedPolicy (wetzelBootstrapTail rest)
  let old := earlierValidated P (wetzelWorkStage a)
  let hP := earlierHistory_persistent_r131 P (wetzelWorkStage a)
  let z := pickedHistoryTrial a old
  let F := wetzelHistoryToWhole rest a
  let t := fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i
  have hTrial := wetzelHistory_readyTrial rest a (wetzelTrialPick a) hReady
  have ht : mapComplexBits F z = t := by simpa only [z,t,pickedHistoryTrial,hpick] using hTrial.2.1
  have hm : F.toFun (pickedHistoryTrialMark a old) = trialValidity t := by
    rw [pickedHistoryTrialMark_eq_ready a old hReady]
    simpa only [z,t,pickedHistoryTrial,hpick] using hTrial.2.2
  let Y := earlierWetzelSiteInHistory a old hP (fun d _ => actualHistorySites d)
  let y := actualHistorySites a old
  have hd : pickedHistoryTrialMark a old ≤
      (⨆ j : {j : GroundContinuumSuccIndex // j<a},z.name =ᴮ (Y j).name) ⊔
      (z.name =ᴮ y.name) :=
    (actualHistorySites_in_native_prefix rest a (hB a)).2.2
  have hLift := F.monotone hd
  rw [hm,F.map_sup_r93,F.map_iSup] at hLift
  refine hLift.trans (sup_le ?_ ?_)
  · apply iSup_le
    intro j
    rw [← mapComplexBits_eqTruth930 F z (Y j),ht]
    change (t.name =ᴮ (mapComplexBits F (Y j)).name) ≤ _
    have he : mapComplexBits F (Y j) = nativeWetzelFinalSite rest j.val :=
      nativeWetzelFinalSite_eq_earlier rest a j
    rw [he]
    exact le_iSup (fun l : GroundContinuumSuccIndex => t.name =ᴮ (nativeWetzelFinalSite rest l).name) j.val
  · rw [← mapComplexBits_eqTruth930 F z y,ht]
    exact le_iSup (fun j : GroundContinuumSuccIndex => t.name =ᴮ (nativeWetzelFinalSite rest j).name) a

theorem nativeWetzelFinalSite_covers (rest : WetzelTailPolicy)
    (hB : ∀ a : GroundContinuumSuccIndex,
      BoundsSmallKappaNames (PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)))
    (hQ : ForcesRelativeCCC (nativeWetzelWholeQ rest))
    (z : ComplexBits (TotalBA (nativeWetzelWholeQ rest)))
    (m : TotalBA (nativeWetzelWholeQ rest)) (hm : z.CutOn m) :
    m ≤ ⨆ j : GroundContinuumSuccIndex,z.name =ᴮ (nativeWetzelFinalSite rest j).name := by
  refine (fixedWetzelPlacementBook.trialsCover (nativeWetzelWholeQ rest) hQ z m hm).trans ?_
  apply iSup_le
  intro i
  let t := fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i
  change (z.name =ᴮ t.name) ⊓ trialValidity t ≤ _
  refine (inf_le_inf le_rfl (nativeWetzelFinalSite_captures_trial rest hB i)).trans ?_
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  exact (bSet.bv_trans inf_le_left inf_le_right).trans (le_iSup (fun l : GroundContinuumSuccIndex => z.name =ᴮ (nativeWetzelFinalSite rest l).name) j)

end JSP000930.Negative
