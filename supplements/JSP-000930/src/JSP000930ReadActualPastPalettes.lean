import JSP000930HistoricalWorkingPalettes

namespace JSP000930.Negative

open JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.PreparedModel JSP000933.FiniteSupport
open JSP000933.ForcingTransport JSP000933.BooleanCompletion

abbrev WetzelWorkingRule (a : GroundContinuumSuccIndex) :=
  (old : WetzelHistory (wetzelWorkStage a)) → WetzelWorkInputs (RO (GoodPrefix old))

abbrev WetzelPriorRules (a : GroundContinuumSuccIndex) :=
  ∀ j : GroundContinuumSuccIndex,j<a → WetzelWorkingRule j

theorem historyStartsWithBulk_sub {a j : GroundContinuumSuccIndex} (hja : j≤a)
    (old : WetzelHistory (wetzelWorkStage a)) (hInit : HistoryStartsWithBulk (a := a) old) :
    HistoryStartsWithBulk (a := j) (subHistory ((wetzelWorkStage_le_iff _ _).mpr hja) old) := hInit

noncomputable def workingSiteAt (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (j : GroundContinuumSuccIndex) :
    ComplexBits (RO (GoodPrefix old)) := by
  classical
  exact if hj : j<a then
    if hP : HistoryPersistent old then
      earlierWetzelSiteInHistory a old hP (fun d _ => actualHistorySites d) ⟨j,hj⟩
    else ComplexBits.checked (0 : ℂ)
  else if j=a then actualHistorySites a old else ComplexBits.checked (0 : ℂ)

theorem workingSiteAt_of_lt {a j : GroundContinuumSuccIndex}
    (old : WetzelHistory (wetzelWorkStage a)) (hj : j<a) (hP : HistoryPersistent old) :
    workingSiteAt a old j =
      earlierWetzelSiteInHistory a old hP (fun d _ => actualHistorySites d) ⟨j,hj⟩ := by
  classical
  simp only [workingSiteAt,dite_eq_left hj,dite_eq_left hP]

theorem workingSiteAt_self (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) :
    workingSiteAt a old a = actualHistorySites a old := by
  classical
  simp [workingSiteAt]

theorem workingSiteAt_proper (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (j : GroundContinuumSuccIndex) :
    (workingSiteAt a old j).CutOn ⊤ := by
  classical
  unfold workingSiteAt
  split
  · rename_i hj
    split
    · rename_i hP
      let hc := ((wetzelWorkStage_lt_iff _ _).mpr hj).le
      let F := historyCompleteEmbed hc old hP
      have h := properSite_map F (actualHistorySites j (subHistory hc old)) (actualHistorySites_proper j _)
      rwa [F.map_top] at h
    · exact ComplexBits.checked_cutOn 0 ⊤
  · split
    · exact actualHistorySites_proper a old
    · exact ComplexBits.checked_cutOn 0 ⊤

abbrev pastWorkCut {j a : GroundContinuumSuccIndex} (h : j<a) :
    wetzelWorkStage j ≤ wetzelWorkStage a := ((wetzelWorkStage_lt_iff _ _).mpr h).le

abbrev pastWorkNextCut {j a : GroundContinuumSuccIndex} (h : j<a) :
    wetzelWorkStage (wetzelGroundNext j) ≤ wetzelWorkStage a :=
  (wetzelWorkStage_le_iff _ _).mpr (wetzelGroundNext_le_of_lt h)

theorem actual_work_lt_successor (j : GroundContinuumSuccIndex) :
    wetzelWorkStage j < wetzelWorkStage (wetzelGroundNext j) :=
  (wetzelWork_next j (wetzelWorkStage j)).mpr le_rfl

noncomputable def pastWorkInputs {a j : GroundContinuumSuccIndex}
    (prior : WetzelPriorRules a) (old : WetzelHistory (wetzelWorkStage a)) (hj : j<a) :
    WetzelWorkInputs (RO (GoodPrefix (subHistory (pastWorkCut hj) old))) :=
  prior j hj (subHistory (pastWorkCut hj) old)

def PastWorkAdmitted {a j : GroundContinuumSuccIndex}
    (prior : WetzelPriorRules a) (old : WetzelHistory (wetzelWorkStage a)) (hj : j<a) : Prop :=
  HistoricalAdmission (subHistory (pastWorkNextCut hj) old) (actual_work_lt_successor j)
    ((pastWorkInputs prior old hj).stage j)

noncomputable def readPastPalette {a j : GroundContinuumSuccIndex}
    (prior : WetzelPriorRules a) (old : WetzelHistory (wetzelWorkStage a)) (hj : j<a)
    (hP : HistoryPersistent old) (hInit : HistoryStartsWithBulk (a := a) old)
    (hA : PastWorkAdmitted prior old hj)
    (r : GroundContinuumSuccIndex) (n : ℕ) : ComplexBits (RO (GoodPrefix old)) :=
  let Later := subHistory (pastWorkNextCut hj) old
  let hLater := subHistory_persistent (pastWorkNextCut hj) old hP
  let Prior := subHistory (pastWorkCut hj) old
  let hPrior := subHistory_persistent (pastWorkCut hj) old hP
  let W := pastWorkInputs prior old hj
  let F := wetzelHistoryPreparedMap j Prior hPrior (historyStartsWithBulk_sub hj.le old hInit)
  mapComplexBits (historyCompleteEmbed (pastWorkNextCut hj) old hP)
    (historicalMixedPalette
      (old := Later) ((wetzelGroundNext_spec j j).mpr le_rfl) hLater W hA
      (wetzelWork_next j) F r n)

noncomputable def historyPaletteAt (a : GroundContinuumSuccIndex)
    (prior : WetzelPriorRules a) (old : WetzelHistory (wetzelWorkStage a))
    (r j : GroundContinuumSuccIndex) (n : ℕ) : ComplexBits (RO (GoodPrefix old)) := by
  classical
  exact if hj : j<a then
    if hh : HistoryPersistent old ∧ HistoryStartsWithBulk (a := a) old ∧ PastWorkAdmitted prior old hj
    then readPastPalette prior old hj hh.1 hh.2.1 hh.2.2 r n
    else ComplexBits.checked (0 : ℂ)
  else ComplexBits.checked (0 : ℂ)

theorem historyPaletteAt_of_admitted {a j : GroundContinuumSuccIndex}
    (prior : WetzelPriorRules a) (old : WetzelHistory (wetzelWorkStage a)) (hj : j<a)
    (hP : HistoryPersistent old) (hInit : HistoryStartsWithBulk (a := a) old)
    (hA : PastWorkAdmitted prior old hj) (r : GroundContinuumSuccIndex) (n : ℕ) :
    historyPaletteAt a prior old r j n = readPastPalette prior old hj hP hInit hA r n := by
  classical
  simp only [historyPaletteAt,dite_eq_left hj,dite_eq_left (show HistoryPersistent old ∧
    HistoryStartsWithBulk (a := a) old ∧ PastWorkAdmitted prior old hj from ⟨hP,hInit,hA⟩)]

end JSP000930.Negative
