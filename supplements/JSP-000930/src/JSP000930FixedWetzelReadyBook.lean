import JSP000930ActualWetzelPlacementSystem
import JSP000930NegativeReadyTrialScheduling

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport

instance wetzelWholeTrace_nonempty : Nonempty WetzelWholeTrace := ⟨RawTail.empty⟩

noncomputable def fixedWetzelPlacementBook : PlacementBook WetzelWholeTrace :=
  Classical.choice (exists_placementBook wetzelWholeTail_card)

noncomputable def wetzelTrialPick : GroundContinuumSuccIndex → PlacementTrialIndex :=
  Classical.choose (fixedWetzelPlacementBook.exists_readyTrialSchedule wetzelScope)

theorem wetzelTrial_ready_cofinally (i : PlacementTrialIndex) (a : GroundContinuumSuccIndex) :
    ∃ j,a<j ∧ wetzelTrialPick j=i ∧ fixedWetzelPlacementBook.TrialReady wetzelScope j i :=
  Classical.choose_spec (fixedWetzelPlacementBook.exists_readyTrialSchedule wetzelScope) i a

theorem nativeWetzel_readyTrial (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (h : fixedWetzelPlacementBook.TrialReady wetzelScope a (wetzelTrialPick a)) :
    ∃ z : ComplexBits (JSP000933.MarkedForcing.TotalBA
      (nativeWetzelPrefixQ rest (wetzel_bot_lt_work a))),
      z.CutOn (trialValidity z) ∧
      mapComplexBits (wetzelPrefixToWhole rest (wetzel_bot_lt_work a)) z =
        fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) (wetzelTrialPick a) ∧
      (wetzelPrefixToWhole rest (wetzel_bot_lt_work a)).toFun (trialValidity z) =
        trialValidity (fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) (wetzelTrialPick a)) :=
  (nativeWetzelPlacementSystem rest).readyTrial_at fixedWetzelPlacementBook (wetzelTrialPick a) a h

end JSP000930.Negative
