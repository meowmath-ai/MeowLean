import JSP000930HistoryRecursiveSites

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

theorem wetzelHistoryChart_map_between (rest : WetzelTailPolicy)
    {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (x : PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)) :
    let T := wetzelBootstrapTail rest
    let P := basedPolicy T
    let hs := (wetzelWorkStage_le_iff _ _).mpr hab
    wetzelHistoryChart rest (wetzelWorkStage b)
      ((historyCompleteEmbed hs (earlierValidated P (wetzelWorkStage b))
        (earlierHistory_persistent_r131 P _)).toFun x) =
      (prefixReduction hs).boolPullback (wetzelHistoryChart rest (wetzelWorkStage a) x) := by
  let T := wetzelBootstrapTail rest
  let P := basedPolicy T
  let a' := wetzelWorkStage a
  let b' := wetzelWorkStage b
  let hs : a'≤b' := (wetzelWorkStage_le_iff _ _).mpr hab
  let eb := prefixOrderIso_r85 P b'
  let ea := prefixOrderIso_r85 P a'
  let F := wetzelHistoryChart rest b'
  let G := wetzelHistoryChart rest a'
  let H := historyCompleteEmbed hs (earlierValidated P b') (earlierHistory_persistent_r131 P b')
  change F (H.toFun x) = (prefixReduction hs).boolPullback (G x)
  have htest (p : BasedBefore T b') :
      imageCondition p ≤ F (H.toFun x) ↔
        imageCondition p ≤ (prefixReduction hs).boolPullback (G x) := by
    have hL : imageCondition p ≤ F (H.toFun x) ↔ imageCondition (eb p) ≤ H.toFun x := by
      rw [← orderIso_pull_imageCondition930 eb p]
      exact F.le_iff_le
    have hR : imageCondition (restrict p.val a') ≤ G x ↔
        imageCondition (ea (restrict p.val a')) ≤ x := by
      rw [← orderIso_pull_imageCondition930 ea (restrict p.val a')]
      exact G.le_iff_le
    apply hL.trans
    apply (image_le_historyCompleteEmbed hs (earlierValidated P b')
      (earlierHistory_persistent_r131 P b') (eb p) x).trans
    have he : historyCutPrefix hs (earlierValidated P b')
        (earlierHistory_persistent_r131 P b') (eb p) = ea (restrict p.val a') :=
      goodPrefix_eq_of_trace _ _ rfl
    rw [he]
    exact hR.symm.trans (image_le_regular_pullback (prefixReduction hs) p (G x)).symm
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

theorem wetzelHistoryToWhole_chart (rest : WetzelTailPolicy) (a : GroundContinuumSuccIndex)
    (x : PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)) :
    nativeWetzelWholePull rest ((wetzelHistoryToWhole rest a).toFun x) =
      (wholeReduction (R := iterationRules (basedPolicy (wetzelBootstrapTail rest)))
        (wetzelWorkStage a)).boolPullback (wetzelHistoryChart rest (wetzelWorkStage a) x) := by
  let T := wetzelBootstrapTail rest
  let F := nativeWetzelWholePull rest
  let G := nativeWetzelPrefixPull rest (wetzel_bot_lt_work a)
  let E := wetzelHistoryChart rest (wetzelWorkStage a)
  change F (F.symm ((wholeReduction (R := iterationRules (basedPolicy T)) (wetzelWorkStage a)).boolPullback
      (G (G.symm (E x))))) = _
  rw [F.apply_symm_apply,G.apply_symm_apply]

theorem whole_after_prefixReduction930 {A T : Type} [LinearOrder A] [Preorder T]
    {R : Rules (fun (_ : A) => T)} {a b : A} (hab : a≤b) (v : RO (Before R a)) :
    (wholeReduction b).boolPullback ((prefixReduction hab).boolPullback v) =
      (wholeReduction a).boolPullback v := by
  have htest (p : Condition R) :
      imageCondition p ≤ (wholeReduction b).boolPullback ((prefixReduction hab).boolPullback v) ↔
        imageCondition p ≤ (wholeReduction a).boolPullback v := by
    rw [image_le_regular_pullback,image_le_regular_pullback,image_le_regular_pullback]
    have he : restrict (restrict p b).val a = restrict p a := restrict_restrict_r92 p hab
    change imageCondition (restrict (restrict p b).val a) ≤ v ↔
      imageCondition (restrict p a) ≤ v
    rw [he]
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

theorem wetzelHistoryToWhole_commutes (rest : WetzelTailPolicy) {a b : GroundContinuumSuccIndex}
    (hab : a≤b) (x : PreStageAlgebra (wetzelBootstrapTail rest) (a := wetzelWorkStage a)) :
    let P := basedPolicy (wetzelBootstrapTail rest)
    let hs := (wetzelWorkStage_le_iff _ _).mpr hab
    (wetzelHistoryToWhole rest b).toFun
      ((historyCompleteEmbed hs (earlierValidated P (wetzelWorkStage b))
        (earlierHistory_persistent_r131 P _)).toFun x) =
      (wetzelHistoryToWhole rest a).toFun x := by
  dsimp only
  apply (nativeWetzelWholePull rest).injective
  rw [wetzelHistoryToWhole_chart,wetzelHistoryToWhole_chart]
  rw [wetzelHistoryChart_map_between rest hab x]
  exact whole_after_prefixReduction930 _ _

end JSP000930.Negative
