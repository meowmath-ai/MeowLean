import JSP000930ReadActualPastPalettes

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.BooleanNames

noncomputable def buildWorkingInputs (a : GroundContinuumSuccIndex)
    (prior : WetzelPriorRules a) : WetzelWorkingRule a :=
  fun old => ⟨workingSiteAt a old,historyPaletteAt a prior old a⟩

noncomputable def actualWetzelWorkingRule (a : GroundContinuumSuccIndex) : WetzelWorkingRule a :=
  WellFounded.fix wellFounded_lt buildWorkingInputs a

theorem actualWetzelWorkingRule_unfold (a : GroundContinuumSuccIndex) :
    actualWetzelWorkingRule a =
      buildWorkingInputs a (fun j _ => actualWetzelWorkingRule j) :=
  WellFounded.fix_eq wellFounded_lt buildWorkingInputs a

noncomputable def actualWetzelRest : WetzelTailPolicy
  | none, _ => fun _ => ⊤
  | some none, _ => fun _ => ⊤
  | some (some a), old => by
    let o : WetzelHistory (wetzelWorkStage a) := old
    letI : Nonempty (GoodPrefix o) := wetzelGoodPrefix_nonempty o
    exact CertifiedStageLabel.admits ((actualWetzelWorkingRule a o).stage a)

noncomputable abbrev actualWetzelTail := wetzelBootstrapTail actualWetzelRest
noncomputable abbrev actualWetzelPolicy := basedPolicy actualWetzelTail

abbrev ActualWorkOld (a : GroundContinuumSuccIndex) :=
  earlierValidated actualWetzelPolicy (wetzelWorkStage a)

abbrev ActualWorkBA (a : GroundContinuumSuccIndex) := RO (GoodPrefix (ActualWorkOld a))

noncomputable def actualWorkingInputs (a : GroundContinuumSuccIndex) : WetzelWorkInputs (ActualWorkBA a) :=
  actualWetzelWorkingRule a (ActualWorkOld a)

theorem actualWetzelTail_admits_at_old (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) :
    actualWetzelTail (wetzelWorkStage a) old =
      CertifiedStageLabel.admits ((actualWetzelWorkingRule a old).stage a) := by
  change wetzelBootstrapTail actualWetzelRest (wetzelWorkStage a) old = _
  rw [wetzelBootstrapTail_work]
  rfl

theorem actualWetzelTail_stageValues (a : GroundContinuumSuccIndex) :
    TailStageValues actualWetzelTail (a := wetzelWorkStage a) =
      CertifiedStageLabel.admits ((actualWorkingInputs a).stage a) :=
  actualWetzelTail_admits_at_old a _

theorem nativeWetzel_pastAdmitted (a : GroundContinuumSuccIndex)
    {j : GroundContinuumSuccIndex} (hj : j<a) :
    PastWorkAdmitted (fun d _ => actualWetzelWorkingRule d) (ActualWorkOld a) hj := by
  change HistoricalAdmission (ActualWorkOld (wetzelGroundNext j)) (actual_work_lt_successor j)
    ((actualWorkingInputs j).stage j)
  exact historicalAdmission_of_native actualWetzelTail (wetzelWorkStage_ne_bot j)
    (actual_work_lt_successor j) ((actualWorkingInputs j).stage j) (actualWetzelTail_stageValues j)

end JSP000930.Negative
