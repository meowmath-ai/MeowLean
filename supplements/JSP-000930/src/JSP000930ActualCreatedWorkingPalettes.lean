import JSP000930NativePreparedHistoryMasks

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Negative.Cohen JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing

abbrev ActualWorkCohenBA (j : GroundContinuumSuccIndex) :=
  WetzelWorkCohenAlgebra (actualWorkingInputs j) j

noncomputable def createdCohenToHistory (j : GroundContinuumSuccIndex) :
    CompleteValueMap (ActualWorkCohenBA j) (ActualWorkBA (wetzelGroundNext j)) :=
  historicalWorkCohenEmbed (old := ActualWorkOld (wetzelGroundNext j))
    ((wetzelGroundNext_spec j j).mpr le_rfl) (earlierHistory_persistent_r131 actualWetzelPolicy _)
    (actualWorkingInputs j) (nativeWetzel_pastAdmitted (wetzelGroundNext j)
      ((wetzelGroundNext_spec j j).mpr le_rfl)) (wetzelWork_next j)

noncomputable def actualWorkPreparedAfterRow (j : GroundContinuumSuccIndex) :
    CompleteValueMap PreparedBA (TotalBA ((actualWorkingInputs j).row j)) :=
  composeCompleteValueMaps (actualPreparedAt j)
    (markedCompleteValueMap ((actualWorkingInputs j).row j))

noncomputable def actualWorkPaletteLabel (j r : GroundContinuumSuccIndex) :
    Label (TotalBA ((actualWorkingInputs j).row j)) :=
  transportLabel (actualWorkPreparedAfterRow j) (preparedWetzelRows r j)

noncomputable def createdWetzelMixedPalette (j r : GroundContinuumSuccIndex) (n : ℕ) :
    ComplexBits (ActualWorkBA (wetzelGroundNext j)) :=
  mapComplexBits (createdCohenToHistory j) (actualMixedPalette (actualWorkPaletteLabel j r) n)

noncomputable def createdWetzelPurePalette (j : GroundContinuumSuccIndex) (r : OmegaOneIndex) (n : ℕ) :
    ComplexBits (ActualWorkBA (wetzelGroundNext j)) :=
  mapComplexBits (createdCohenToHistory j)
    (paletteBits (B := TotalBA ((actualWorkingInputs j).row j)) r n)

noncomputable def actualWetzelRowPalette (a r j : GroundContinuumSuccIndex) (n : ℕ) :
    ComplexBits (ActualWorkBA a) :=
  historyPaletteAt a (fun d _ => actualWetzelWorkingRule d) (ActualWorkOld a) r j n

theorem actualWorkingInputs_site_eq (a : GroundContinuumSuccIndex) :
    (actualWorkingInputs a).site = workingSiteAt a (ActualWorkOld a) := by
  unfold actualWorkingInputs
  rw [actualWetzelWorkingRule_unfold] <;> rfl

theorem actualWorkingInputs_palette_eq (a : GroundContinuumSuccIndex) :
    (actualWorkingInputs a).palette = actualWetzelRowPalette a a := by
  unfold actualWorkingInputs
  rw [actualWetzelWorkingRule_unfold] <;> rfl

theorem actualWetzelRowPalette_eq_map {a j : GroundContinuumSuccIndex} (hj : j<a)
    (r : GroundContinuumSuccIndex) (n : ℕ) :
    actualWetzelRowPalette a r j n =
      mapComplexBits (actualHistoryShift (wetzelGroundNext_le_of_lt hj))
        (createdWetzelMixedPalette j r n) := by
  unfold actualWetzelRowPalette
  rw [historyPaletteAt_of_admitted _ _ hj
    (earlierHistory_persistent_r131 actualWetzelPolicy _)
    (nativeHistory_startsWithBulk actualWetzelRest a) (nativeWetzel_pastAdmitted a hj)] <;> rfl

theorem actualWork_mark_separatesPalette {j r s : GroundContinuumSuccIndex} {u : PreparedBA}
    (h : u ≤ (labelAgreement (preparedWetzelRows r j) (preparedWetzelRows s j))ᶜ) :
    (actualWorkPreparedAfterRow j).toFun u ≤
      (labelAgreement (actualWorkPaletteLabel j r) (actualWorkPaletteLabel j s))ᶜ := by
  unfold actualWorkPaletteLabel
  rw [labelAgreement_transport,← (actualWorkPreparedAfterRow j).map_compl]
  exact (actualWorkPreparedAfterRow j).monotone h

end JSP000930.Negative
