import JSP000930HistoricalWorkingAlgebra
import JSP000930CoherentPreparedPalettes

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Negative.Cohen
open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing

noncomputable def wetzelHistoryPreparedMap (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (hP : HistoryPersistent old)
    (hB : HistoryStartsWithBulk (a := a) old) :
    CompleteValueMap PreparedBA (RO (GoodPrefix old)) :=
  composeCompleteValueMaps (markedCompleteValueMap (valuedCohen PreparedBA WetzelCoordinate))
    (wetzelHistoryBulkToPrefix a old hP hB)

variable {j k : GroundContinuumSuccIndex}
variable {old : WetzelHistory (wetzelWorkStage k)}
variable (h : j<k) (hP : HistoryPersistent old)

abbrev WorkEarlierH := (wetzelWorkStage_lt_iff j k).mpr h

variable (W : WetzelWorkInputs (HistoryPrefixAlgebra old (WorkEarlierH h).le))
variable (hQ : HistoricalAdmission old (WorkEarlierH h) (W.stage j))

noncomputable def historicalWorkCohenEmbed
    (succ : ∀ i : WetzelStageIndex,i<wetzelWorkStage k ↔ i≤wetzelWorkStage j) :
    CompleteValueMap (WetzelWorkCohenAlgebra W j) (RO (GoodPrefix old)) :=
  composeCompleteValueMaps (W.cohenToStage j)
    (embedHistoricalIterand old (WorkEarlierH h) hP succ (W.stage j) hQ)

theorem historicalWorkCohenEmbed_base
    (succ : ∀ i : WetzelStageIndex,i<wetzelWorkStage k ↔ i≤wetzelWorkStage j)
    (b : HistoryPrefixAlgebra old (WorkEarlierH h).le) :
    (historicalWorkCohenEmbed h hP W hQ succ).toFun ((W.oldToCohen j).toFun b) =
      (historyCompleteEmbed (WorkEarlierH h).le old hP).toFun b := by
  unfold historicalWorkCohenEmbed
  change (embedHistoricalIterand old (WorkEarlierH h) hP succ (W.stage j) hQ).toFun
    ((W.cohenToStage j).toFun ((W.oldToCohen j).toFun b)) = _
  rw [WetzelWorkInputs.cohenToStage_base,embedHistoricalIterand_base]

noncomputable def historicalPurePalette
    (succ : ∀ i : WetzelStageIndex,i<wetzelWorkStage k ↔ i≤wetzelWorkStage j)
    (r : OmegaOneIndex) (n : ℕ) : ComplexBits (RO (GoodPrefix old)) :=
  mapComplexBits (historicalWorkCohenEmbed h hP W hQ succ)
    (paletteBits (B := TotalBA (W.row j)) r n)

noncomputable def historicalMixedPalette
    (succ : ∀ i : WetzelStageIndex,i<wetzelWorkStage k ↔ i≤wetzelWorkStage j)
    (F : CompleteValueMap PreparedBA (HistoryPrefixAlgebra old (WorkEarlierH h).le))
    (r : GroundContinuumSuccIndex) (n : ℕ) : ComplexBits (RO (GoodPrefix old)) :=
  let G := composeCompleteValueMaps F (markedCompleteValueMap (W.row j))
  mapComplexBits (historicalWorkCohenEmbed h hP W hQ succ)
    (actualMixedPalette (transportLabel G (preparedWetzelRows r j)) n)

end JSP000930.Negative
