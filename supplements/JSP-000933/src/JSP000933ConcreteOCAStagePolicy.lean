import JSP000933EligibleStageChoice

namespace JSP000933
namespace CantorCodes

open BooleanCompletion BooleanTwoStep FiniteSupport OpenGraphForcing

noncomputable def ocaStagePolicy (P : OCAParameters) : StagePolicy OmegaTwoIndex OCALabel := by
  classical
  intro a old
  exact if hp : HistoryPersistent old then
    if hc : BooleanCCC (RO (GoodPrefix old)) then
      if h : Nonempty (StageChoice P a old hp hc) then
        StageChoice.admission P a old hp hc (Classical.choice h)
      else idleAdmission
    else idleAdmission
  else idleAdmission

theorem ocaStagePolicy_active_r164 (P : OCAParameters) (a : OmegaTwoIndex)
    (old : PrefixValidator a OCALabel) (hp : HistoryPersistent old)
    (hc : BooleanCCC (RO (GoodPrefix old))) (h : Nonempty (StageChoice P a old hp hc)) :
    ocaStagePolicy P a old = StageChoice.admission P a old hp hc (Classical.choice h) := by
  classical
  simp only [ocaStagePolicy,dite_eq_left hp,dite_eq_left hc,dite_eq_left h]

theorem ocaStagePolicy_inactive_r164 (P : OCAParameters) (a : OmegaTwoIndex)
    (old : PrefixValidator a OCALabel) (hp : HistoryPersistent old)
    (hc : BooleanCCC (RO (GoodPrefix old))) (h : ¬ Nonempty (StageChoice P a old hp hc)) :
    ocaStagePolicy P a old = idleAdmission := by
  classical
  simp only [ocaStagePolicy,dite_eq_left hp,dite_eq_left hc,dite_eq_right h]

theorem ocaStagePolicy_top_r164 (P : OCAParameters) (a : OmegaTwoIndex)
    (old : PrefixValidator a OCALabel) :
    ocaStagePolicy P a old (⊤ : OCALabel) = ⊤ := by
  classical
  unfold ocaStagePolicy
  split
  · split
    · split
      · exact cliqueAdmitted_empty_r121 _ _ _
      · exact idleAdmission_top_r133
    · exact idleAdmission_top_r133
  · exact idleAdmission_top_r133

theorem ocaStagePolicy_stepCCC_r164 (P : OCAParameters) (a : OmegaTwoIndex)
    (hBefore : HasCountableAntichains (Before (iterationRules (ocaStagePolicy P)) a)) :
    HasCountableAntichains (Condition (StageOf (ocaStagePolicy P) a)) := by
  classical
  let policy := ocaStagePolicy P
  let old := earlierValidated policy a
  have hp : HistoryPersistent old := earlierHistory_persistent_r131 policy a
  have hc : BooleanCCC (RO (GoodPrefix old)) :=
    BooleanCCC_of_completeValueMap_r158 (orderIsoReduction (prefixOrderIso_r85 policy a)).completeValueMap
      (booleanCCC_of_conditionCCC_r66 hBefore)
  change HasCountableAntichains (Condition (staticLabelStage (ocaStagePolicy P a old)))
  by_cases h : Nonempty (StageChoice P a old hp hc)
  · rw [ocaStagePolicy_active_r164 P a old hp hc h]
    exact (Classical.choice h).countableAntichains
  · rw [ocaStagePolicy_inactive_r164 P a old hp hc h]
    exact idleStage_countableAntichains_r133 hc

theorem ocaPrefixCCC_r164 (P : OCAParameters) (a : OmegaTwoIndex) :
    HasCountableAntichains (Before (iterationRules (ocaStagePolicy P)) a) :=
  countableAntichains_allPrefixes_r89 (ocaStagePolicy P)
    (fun a => ocaStagePolicy_top_r164 P a _) (ocaStagePolicy_stepCCC_r164 P) a

theorem ocaIterationCCC_r164 (P : OCAParameters) :
    HasCountableAntichains (IterationCondition (ocaStagePolicy P)) :=
  countableAntichains_omegaTwoIteration_r89 (ocaStagePolicy P)
    (fun a => ocaStagePolicy_top_r164 P a _) (ocaStagePolicy_stepCCC_r164 P)

end CantorCodes
end JSP000933
