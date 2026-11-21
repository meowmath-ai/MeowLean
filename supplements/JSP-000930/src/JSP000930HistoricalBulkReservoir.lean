import JSP000930CheckedSuccessorsAndInfiniteTail

namespace JSP000930.Negative

open JSP000930.Positive.Cohen JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.PreparedModel

noncomputable def idleWetzelTail : WetzelTailPolicy := fun _ _ _ => ⊤

theorem bootstrap_valid_before_work (rest : WetzelTailPolicy) :
    ∀ i : WetzelStageIndex,i≤wetzelBulkStage →
      localStageValid (basedPolicy (wetzelBootstrapTail rest)) i =
        localStageValid (basedPolicy (wetzelBootstrapTail idleWetzelTail)) i := by
  intro i
  have hWF : WellFounded (fun i j : WetzelStageIndex => i < j) := wellFounded_lt
  induction i using hWF.induction with
  | h i ih =>
    intro hi
    let T := wetzelBootstrapTail rest
    let U := wetzelBootstrapTail idleWetzelTail
    have hOld : earlierValidated (basedPolicy T) i = earlierValidated (basedPolicy U) i := by
      funext j hj
      exact ih j hj (hj.le.trans hi)
    funext p s
    apply propext
    rw [localStageValid_unfold_r85,localStageValid_unfold_r85]
    change (rawProjection (earlierValidated (basedPolicy T) i) p ≤
      basedPolicy T i (earlierValidated (basedPolicy T) i) s) ↔
      (rawProjection (earlierValidated (basedPolicy U) i) p ≤
        basedPolicy U i (earlierValidated (basedPolicy U) i) s)
    rw [hOld]
    rcases lt_or_eq_of_le hi with h | h
    · have he := before_wetzelBulk_only_base i h
      subst i
      simp [basedPolicy]
    · subst i
      by_cases h : s.1 = ⊤
      · simp only [basedPolicy,ite_eq_right wetzelBulkStage_ne_bot,ite_eq_left h,T,U,wetzelBootstrapTail_bulk]
      · simp only [basedPolicy,ite_eq_right wetzelBulkStage_ne_bot,ite_eq_right h]

abbrev WetzelBulkHistory :=
  earlierValidated (basedPolicy (wetzelBootstrapTail idleWetzelTail)) (wetzelWorkStage firstGroundWetzelStage)

theorem bootstrap_history_before_work (rest : WetzelTailPolicy) :
    earlierValidated (basedPolicy (wetzelBootstrapTail rest))
      (wetzelWorkStage firstGroundWetzelStage) = WetzelBulkHistory := by
  funext i hi
  exact bootstrap_valid_before_work rest i ((wetzelBulk_next i).mp hi)

noncomputable def checkedBulkToHistory : CompleteValueMap WetzelCohenBA (RO (GoodPrefix WetzelBulkHistory)) :=
  composeCompleteValueMaps (actualWetzelCohen_toNative idleWetzelTail)
    (completeMapOfOrderIso930 (wetzelHistoryChart idleWetzelTail
      (wetzelWorkStage firstGroundWetzelStage)).symm)

def HistoryStartsWithBulk {a : GroundContinuumSuccIndex} (old : WetzelHistory (wetzelWorkStage a)) :
    Prop := subHistory ((wetzelWorkStage_le_iff _ _).mpr (firstGroundWetzelStage_le a)) old =
      WetzelBulkHistory

theorem nativeHistory_startsWithBulk (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex) :
    HistoryStartsWithBulk (a := a)
      (earlierValidated (basedPolicy (wetzelBootstrapTail rest)) (wetzelWorkStage a)) :=
  bootstrap_history_before_work rest

def goodPrefixCongr930 {A T : Type} [LinearOrder A] [Preorder T] {a : A}
    {h k : PrefixValidator a T} (e : h = k) : GoodPrefix h ≃o GoodPrefix k := by
  cases e
  exact OrderIso.refl _

noncomputable def wetzelHistoryBulkToPrefix (a : GroundContinuumSuccIndex)
    (old : WetzelHistory (wetzelWorkStage a)) (hP : HistoryPersistent old)
    (hB : HistoryStartsWithBulk (a := a) old) :
    CompleteValueMap WetzelCohenBA (RO (GoodPrefix old)) :=
  let ha := (wetzelWorkStage_le_iff _ _).mpr (firstGroundWetzelStage_le a)
  let F := (orderIsoReduction (goodPrefixCongr930 hB)).completeValueMap
  composeCompleteValueMaps (composeCompleteValueMaps checkedBulkToHistory F)
    (historyCompleteEmbed ha old hP)

end JSP000930.Negative
