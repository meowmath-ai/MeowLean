import JSP000930ActualFreshCohenStep

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport

theorem freshCohen_at_native_mark (a : GroundContinuumSuccIndex) (u : PreparedBA) :
    createdCohenIsoToHistory a ((stageCohenMap (LiveRowModel a)).toFun
      ((actualWorkPreparedAfterRow a).toFun u)) =
      (actualPreparedAt (wetzelGroundNext a)).toFun u := by
  rw [createdCohenIsoToHistory_apply]
  change (createdCohenToHistory a).toFun (((actualWorkingInputs a).oldToCohen a).toFun
    ((actualPreparedAt a).toFun u)) = _
  rw [createdCohenToHistory_base,actualHistoryShift_prepared]

theorem freshCohen_to_native_oldComplex (a : GroundContinuumSuccIndex) (z : ComplexBits (ActualWorkBA a)) :
    mapComplexBits (createdCohenToHistory a)
      (mapComplexBits (stageCohenMap (LiveRowModel a)) (mapComplexBits (actualWorkRowMap a) z)) =
    mapComplexBits (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le) z :=
  congrArg₂ ComplexBits.mk
    (funext fun q => createdCohenToHistory_base a (z.re q))
    (funext fun q => createdCohenToHistory_base a (z.im q))

theorem freshCohenSite_to_native (a j : GroundContinuumSuccIndex) (hj : j≤a) :
    (cohenSiteLift (beforeFreshSite a) j).map (createdCohenToHistory a) =
      (actualWorkingInputs (wetzelGroundNext a)).site j := by
  change mapComplexBits (createdCohenToHistory a)
    (mapComplexBits (stageCohenMap (LiveRowModel a))
      (mapComplexBits (actualWorkRowMap a) ((actualWorkingInputs a).site j))) = _
  rw [freshCohen_to_native_oldComplex]
  exact actualWorkSite_map_until_self a j hj

theorem freshCohenPalette_to_native (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (r : s) (j : GroundContinuumSuccIndex) (hj : j≤a) (n : ℕ) :
    (extendActualPalette (beforeFreshPalette a s)
      (fun t : s => actualWorkPaletteLabel a t.val) a r j n).map (createdCohenToHistory a) =
      actualWetzelRowPalette (wetzelGroundNext a) r.val j n := by
  rcases lt_or_eq_of_le hj with h|h
  · rw [extendActualPalette_old _ _ _ _ h.ne]
    change mapComplexBits (createdCohenToHistory a)
      (mapComplexBits (stageCohenMap (LiveRowModel a))
        (mapComplexBits (actualWorkRowMap a) (actualWetzelRowPalette a r.val j n))) = _
    rw [freshCohen_to_native_oldComplex]
    exact actualWetzelRowPalette_transport _ h _ _
  · subst j
    rw [extendActualPalette_fresh,actualWetzelRowPalette_at_new]
    rfl

end JSP000930.Negative
