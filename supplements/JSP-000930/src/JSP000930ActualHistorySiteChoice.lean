import JSP000930HistoricalBulkReservoir
import JSP000930NegativeActualBulkReservoir

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion

abbrev WetzelSiteRule (a : GroundContinuumSuccIndex) :=
  (old : WetzelHistory (wetzelWorkStage a)) → ComplexBits (RO (GoodPrefix old))

def HistorySiteGuard (a : GroundContinuumSuccIndex) (old : WetzelHistory (wetzelWorkStage a)) : Prop :=
  HistoryPersistent old ∧ HistoryStartsWithBulk (a := a) old ∧
    BoundsSmallKappaNames (RO (GoodPrefix old))

noncomputable def earlierWetzelSiteInHistory (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (hP : HistoryPersistent old)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d)
    (i : {d : GroundContinuumSuccIndex // d<a}) : ComplexBits (RO (GoodPrefix old)) :=
  let h := ((wetzelWorkStage_lt_iff _ _).mpr i.property).le
  mapComplexBits (historyCompleteEmbed h old hP) (prior i.val i.property (subHistory h old))

noncomputable def pickedHistoryTrial (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) : ComplexBits (RO (GoodPrefix old)) :=
  wetzelHistoryTrial a old (wetzelTrialPick a)

noncomputable def pickedHistoryTrialMark (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) : RO (GoodPrefix old) := by
  classical
  exact if fixedWetzelPlacementBook.TrialReady wetzelScope a (wetzelTrialPick a) then
    trialValidity (pickedHistoryTrial a old) else ⊥

theorem pickedHistoryTrialMark_le (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) :
    pickedHistoryTrialMark a old ≤ trialValidity (pickedHistoryTrial a old) := by
  classical
  unfold pickedHistoryTrialMark
  split
  · exact le_rfl
  · exact bot_le

theorem pickedHistoryTrialMark_eq_ready (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a))
    (h : fixedWetzelPlacementBook.TrialReady wetzelScope a (wetzelTrialPick a)) :
    pickedHistoryTrialMark a old = trialValidity (pickedHistoryTrial a old) := by
  classical
  simp only [pickedHistoryTrialMark,ite_eq_left h]

def ActualHistorySiteChoice (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (hP : HistoryPersistent old)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d)
    (y : ComplexBits (RO (GoodPrefix old))) : Prop :=
  y.CutOn ⊤ ∧ (∀ i : {d : GroundContinuumSuccIndex // d<a},
    (y.name =ᴮ (earlierWetzelSiteInHistory a old hP prior i).name) = ⊥) ∧
    pickedHistoryTrialMark a old ≤
      (⨆ i : {d : GroundContinuumSuccIndex // d<a},
        (pickedHistoryTrial a old).name =ᴮ (earlierWetzelSiteInHistory a old hP prior i).name) ⊔
      ((pickedHistoryTrial a old).name =ᴮ y.name)

theorem exists_actualHistorySiteChoice (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (h : HistorySiteGuard a old)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d) :
    ∃ y,ActualHistorySiteChoice a old h.1 prior y := by
  exact exists_newSite_with_actual_bulk_reservoir h.2.2
    (continuumSuccInitial_card_lt_r406 a) (wetzelHistoryBulkToPrefix a old h.1 h.2.1)
    (earlierWetzelSiteInHistory a old h.1 prior) (pickedHistoryTrial a old)
    (pickedHistoryTrialMark a old) ((le_trialValidity_iff _ _).mp (pickedHistoryTrialMark_le a old))

noncomputable def actualHistorySiteStep (a : GroundContinuumSuccIndex)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d) : WetzelSiteRule a := by
  classical
  intro old
  exact if h : HistorySiteGuard a old then Classical.choose (exists_actualHistorySiteChoice a old h prior)
    else ComplexBits.checked (0 : ℂ)

theorem actualHistorySiteStep_spec (a : GroundContinuumSuccIndex)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d)
    (old : WetzelHistory (wetzelWorkStage a)) (h : HistorySiteGuard a old) :
    ActualHistorySiteChoice a old h.1 prior (actualHistorySiteStep a prior old) := by
  classical
  rw [actualHistorySiteStep,dite_eq_left h]
  exact Classical.choose_spec (exists_actualHistorySiteChoice a old h prior)

theorem actualHistorySiteStep_proper (a : GroundContinuumSuccIndex)
    (prior : ∀ d : GroundContinuumSuccIndex,d<a → WetzelSiteRule d)
    (old : WetzelHistory (wetzelWorkStage a)) : (actualHistorySiteStep a prior old).CutOn ⊤ := by
  classical
  by_cases h : HistorySiteGuard a old
  · exact (actualHistorySiteStep_spec a prior old h).1
  · rw [actualHistorySiteStep,dite_eq_right h]
    exact ComplexBits.checked_cutOn 0 ⊤

end JSP000930.Negative
