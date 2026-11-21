import JSP000930HistoricalPlacementRectangles

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.PreparedModel
open JSP000933.OpenGraphForcing JSP000933.RelativeOCA JSP000933.CantorCodes

noncomputable def wetzelHistoryPlacementRow (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (i : PlacementTableIndex) :
    ℕ → RO (GoodPrefix old) :=
  fun n => ⨆ r : {s : OmegaOneIndex // s < i.2.1},⨆ j : ClosedKappaCut i.1,
    historyRectangle old (fixedWetzelPlacementBook.trace j.val)
      (decodeCutCode i.2.1 (fixedWetzelPlacementBook.preparedReals i.2.2) (n,r) ⊓
        firstTracePlacement (fixedWetzelPlacementBook.mixed i.1) r.val j)

noncomputable def wetzelHistoryTrial (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (i : PlacementTrialIndex) :
    ComplexBits (RO (GoodPrefix old)) :=
  decodeTrial (wetzelHistoryPlacementRow a old i.1) (wetzelHistoryPlacementRow a old i.2)

noncomputable def wetzelHistoryToPrefix (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex) :
    CompleteValueMap
      (RO (GoodPrefix (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a))))
      (TotalBA (nativeWetzelPrefixQ rest (wetzel_bot_lt_work a))) :=
  completeMapOfOrderIso930 ((wetzelHistoryChart rest (wetzelWorkStage a)).trans
      (nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)).symm)

theorem wetzelHistoryToPrefix_row (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (i : PlacementTableIndex)
    (h : ∀ j : ClosedKappaCut i.1,TraceBelow wetzelScope a (fixedWetzelPlacementBook.trace j.val))
    (n : ℕ) :
    (wetzelHistoryToPrefix rest a).toFun
      (wetzelHistoryPlacementRow a
        (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) i n) =
      (nativeWetzelPlacementSystem rest).localRow fixedWetzelPlacementBook i a h n := by
  let F := wetzelHistoryToPrefix rest a
  have he (j : ClosedKappaCut i.1) (m : PreparedBA) :
      F.toFun (historyRectangle _ (fixedWetzelPlacementBook.trace j.val) m) =
        traceRectangle (nativeWetzelPrefixQ rest (wetzel_bot_lt_work a))
          (wetzelEarlierTrace a (fixedWetzelPlacementBook.trace j.val) (h j)) m := by
    apply (nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)).injective
    change nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)
      ((nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)).symm (_)) = _
    rw [OrderIso.apply_symm_apply]
    exact wetzelHistoryChart_rectangle rest a _ (h j) m
  dsimp only [F] at he
  simp only [wetzelHistoryPlacementRow,(wetzelHistoryToPrefix rest a).map_iSup,PlacementPrefixSystem.localRow,
    placementTableReal,nativeWetzelPlacementSystem,he]
  rfl

noncomputable def wetzelHistoryToWhole (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex) :
    CompleteValueMap
      (RO (GoodPrefix (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a))))
      (TotalBA (nativeWetzelWholeQ rest)) :=
  composeCompleteValueMaps (wetzelHistoryToPrefix rest a)
    (wetzelPrefixToWhole rest (wetzel_bot_lt_work a))

theorem wetzelHistoryToWhole_row (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (i : PlacementTableIndex)
    (h : ∀ j : ClosedKappaCut i.1,TraceBelow wetzelScope a (fixedWetzelPlacementBook.trace j.val))
    (n : ℕ) :
    (wetzelHistoryToWhole rest a).toFun
      (wetzelHistoryPlacementRow a
        (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) i n) =
    fixedWetzelPlacementBook.row (nativeWetzelWholeQ rest) i n := by
  change (wetzelPrefixToWhole rest (wetzel_bot_lt_work a)).toFun
    ((wetzelHistoryToPrefix rest a).toFun (wetzelHistoryPlacementRow a _ i n)) = _
  rw [wetzelHistoryToPrefix_row rest a i h n]
  exact (nativeWetzelPlacementSystem rest).localRow_commutes fixedWetzelPlacementBook i a h n

theorem wetzelHistory_readyTrial (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (i : PlacementTrialIndex) (h : fixedWetzelPlacementBook.TrialReady wetzelScope a i) :
    let z := wetzelHistoryTrial a
      (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) i
    z.CutOn (trialValidity z) ∧
      mapComplexBits (wetzelHistoryToWhole rest a) z =
        fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i ∧
      (wetzelHistoryToWhole rest a).toFun (trialValidity z) =
        trialValidity (fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i) := by
  let z := wetzelHistoryTrial a
    (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) i
  let F := wetzelHistoryToWhole rest a
  have he : mapComplexBits F z = fixedWetzelPlacementBook.trial (nativeWetzelWholeQ rest) i :=
    decodeTrial_commutes F _ _ _ _ (wetzelHistoryToWhole_row rest a i.1 h.1)
      (wetzelHistoryToWhole_row rest a i.2 h.2)
  exact ⟨(le_trialValidity_iff _ _).mp le_rfl,he,
    (trialValidity_map F z).trans (congrArg trialValidity he)⟩

end JSP000930.Negative
