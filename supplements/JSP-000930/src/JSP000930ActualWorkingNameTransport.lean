import JSP000930ActualCreatedWorkingPalettes

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

theorem actualHistoryShift_trans {a b c : GroundContinuumSuccIndex} (hab : a≤b) (hbc : b≤c)
    (v : ActualWorkBA a) :
    (actualHistoryShift hbc).toFun ((actualHistoryShift hab).toFun v) =
      (actualHistoryShift (hab.trans hbc)).toFun v :=
  historyCompleteEmbed_comp_exact ((wetzelWorkStage_le_iff _ _).mpr hab)
    ((wetzelWorkStage_le_iff _ _).mpr hbc) (ActualWorkOld c)
    (earlierHistory_persistent_r131 actualWetzelPolicy _) v

theorem actualHistoryShift_self (a : GroundContinuumSuccIndex) (v : ActualWorkBA a) :
    (actualHistoryShift (le_refl a)).toFun v = v := by
  let old := ActualWorkOld a
  let h := (wetzelWorkStage_le_iff _ _).mpr (le_refl a)
  let hP := earlierHistory_persistent_r131 actualWetzelPolicy (wetzelWorkStage a)
  have hTest (p : GoodPrefix old) :
      imageCondition p ≤ (actualHistoryShift (le_refl a)).toFun v ↔ imageCondition p ≤ v := by
    change imageCondition p ≤ (historyCompleteEmbed h old hP).toFun v ↔ _
    apply (image_le_historyCompleteEmbed h old hP p v).trans
    have hp : historyCutPrefix h old hP p = p := by
      classical
      apply goodPrefix_eq_of_trace930
      exact cut_eq_self_of_bounded_r86 p.bounded
    exact Iff.of_eq (congrArg (fun q => imageCondition q ≤ v) hp)
  exact le_antisymm (le_of_image_tests (fun p => (hTest p).mp))
    (le_of_image_tests (fun p => (hTest p).mpr))

theorem mapComplexBits_comp930 {B C D : Type} [NontrivialCompleteBooleanAlgebra B]
    [NontrivialCompleteBooleanAlgebra C] [NontrivialCompleteBooleanAlgebra D]
    (F : CompleteValueMap B C) (G : CompleteValueMap C D) (z : ComplexBits B) :
    mapComplexBits G (mapComplexBits F z) = mapComplexBits (composeCompleteValueMaps F G) z := by
  cases z
  rfl

theorem actualHistoryShift_complex_trans {a b c : GroundContinuumSuccIndex}
    (hab : a≤b) (hbc : b≤c) (z : ComplexBits (ActualWorkBA a)) :
    mapComplexBits (actualHistoryShift hbc) (mapComplexBits (actualHistoryShift hab) z) =
      mapComplexBits (actualHistoryShift (hab.trans hbc)) z :=
  congrArg₂ ComplexBits.mk (funext fun q => actualHistoryShift_trans hab hbc (z.re q))
    (funext fun q => actualHistoryShift_trans hab hbc (z.im q))

theorem actualHistoryShift_complex_self (a : GroundContinuumSuccIndex) (z : ComplexBits (ActualWorkBA a)) :
    mapComplexBits (actualHistoryShift (le_refl a)) z = z := by
  cases z with
  | mk x y =>
    exact congrArg₂ ComplexBits.mk (funext fun q => actualHistoryShift_self a (x q))
      (funext fun q => actualHistoryShift_self a (y q))

theorem actualWetzelRowPalette_transport {a b j : GroundContinuumSuccIndex}
    (hab : a≤b) (hj : j<a) (r : GroundContinuumSuccIndex) (n : ℕ) :
    mapComplexBits (actualHistoryShift hab) (actualWetzelRowPalette a r j n) =
      actualWetzelRowPalette b r j n := by
  rw [actualWetzelRowPalette_eq_map hj,actualWetzelRowPalette_eq_map (hj.trans_le hab),
    actualHistoryShift_complex_trans]

theorem actualWetzelRowPalette_at_new (a r : GroundContinuumSuccIndex) (n : ℕ) :
    actualWetzelRowPalette (wetzelGroundNext a) r a n = createdWetzelMixedPalette a r n := by
  rw [actualWetzelRowPalette_eq_map ((wetzelGroundNext_spec a a).mpr le_rfl),
    actualHistoryShift_complex_self]

theorem actualWorkingSite_eq_map {a j : GroundContinuumSuccIndex} (hj : j<a) :
    (actualWorkingInputs a).site j =
      mapComplexBits (actualHistoryShift hj.le) (actualHistorySites j (ActualWorkOld j)) := by
  rw [actualWorkingInputs_site_eq,workingSiteAt_of_lt _ hj
    (earlierHistory_persistent_r131 actualWetzelPolicy _)] <;> rfl

theorem actualWorkingSite_transport {a b j : GroundContinuumSuccIndex}
    (hab : a≤b) (hj : j<a) :
    mapComplexBits (actualHistoryShift hab) ((actualWorkingInputs a).site j) =
      (actualWorkingInputs b).site j := by
  rw [actualWorkingSite_eq_map hj,actualWorkingSite_eq_map (hj.trans_le hab),
    actualHistoryShift_complex_trans]

theorem actualWorkingSite_at_new (a : GroundContinuumSuccIndex) :
    (actualWorkingInputs (wetzelGroundNext a)).site a =
      mapComplexBits (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le)
        ((actualWorkingInputs a).site a) := by
  rw [actualWorkingSite_eq_map ((wetzelGroundNext_spec a a).mpr le_rfl),
    actualWorkingInputs_site_eq,workingSiteAt_self]

end JSP000930.Negative
