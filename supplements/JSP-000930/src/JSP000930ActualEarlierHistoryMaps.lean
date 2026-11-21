import JSP000930ActualBulkProjectedCCC
import JSP000933PartialHistory

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion

variable {A T : Type} [LinearOrder A] [Preorder T] {a b c : A}

theorem goodPrefix_eq_of_trace930 {old : PrefixValidator a T}
    (p q : GoodPrefix old) (h : p.trace = q.trace) : p = q := by
  cases p
  cases q
  cases h
  rfl

def historyCutPrefix (hab : b≤a) (old : PrefixValidator a T) (h : HistoryPersistent old)
    (p : GoodPrefix old) : GoodPrefix (subHistory hab old) :=
  (partialHistoryPrefixIso_r131 hab old h)
    (restrict ((partialHistoryPrefixIso_r131 (le_refl a) old h).symm p).val b)

theorem historyCutPrefix_trace (hab : b≤a) (old : PrefixValidator a T) (h : HistoryPersistent old)
    (p : GoodPrefix old) : (historyCutPrefix hab old h p).trace = cut p.trace b := rfl

theorem historyCutPrefix_mono (hab : b≤a) (old : PrefixValidator a T) (h : HistoryPersistent old) :
    Monotone (historyCutPrefix hab old h) := fun _ _ hk =>
  (partialHistoryPrefixIso_r131 hab old h).monotone
    (restrict_mono_r75 ((partialHistoryPrefixIso_r131 (le_refl a) old h).symm.monotone hk) b)

noncomputable def historyCompleteEmbed (hab : b≤a) (old : PrefixValidator a T)
    (h : HistoryPersistent old) :
    CompleteValueMap (RO (GoodPrefix (subHistory hab old))) (RO (GoodPrefix old)) :=
  composeCompleteValueMaps
    (composeCompleteValueMaps
      (orderIsoReduction (partialHistoryPrefixIso_r131 hab old h)).completeValueMap
      (prefixReduction hab).completeValueMap)
    (orderIsoReduction (partialHistoryPrefixIso_r131 (le_refl a) old h).symm).completeValueMap

theorem image_le_historyCompleteEmbed (hab : b≤a) (old : PrefixValidator a T)
    (h : HistoryPersistent old) (p : GoodPrefix old)
    (u : RO (GoodPrefix (subHistory hab old))) :
    imageCondition p ≤ (historyCompleteEmbed hab old h).toFun u ↔
      imageCondition (historyCutPrefix hab old h p) ≤ u := by
  let R := orderIsoReduction (partialHistoryPrefixIso_r131 (le_refl a) old h).symm
  let S := prefixReduction (R := partialHistoryRules old h) hab
  let U := orderIsoReduction (partialHistoryPrefixIso_r131 hab old h)
  exact (image_le_regular_pullback R p _).trans
    ((image_le_regular_pullback S (R.toFun p) _).trans
      (image_le_regular_pullback U (S.toFun (R.toFun p)) u))

theorem subHistory_persistent (hab : b≤a) (old : PrefixValidator a T) (h : HistoryPersistent old) :
    HistoryPersistent (subHistory hab old) := by
  intro i hi p q s hp hs
  exact h i (hi.trans_le hab) p q s hp hs

theorem historyCompleteEmbed_comp_exact (hcb : c≤b) (hba : b≤a)
    (old : PrefixValidator a T) (hP : HistoryPersistent old)
    (u : RO (GoodPrefix (subHistory (hcb.trans hba) old))) :
    (historyCompleteEmbed hba old hP).toFun
      ((historyCompleteEmbed hcb (subHistory hba old) (subHistory_persistent hba old hP)).toFun u) =
      (historyCompleteEmbed (hcb.trans hba) old hP).toFun u := by
  have htest (p : GoodPrefix old) :
      imageCondition p ≤ (historyCompleteEmbed hba old hP).toFun
        ((historyCompleteEmbed hcb (subHistory hba old) (subHistory_persistent hba old hP)).toFun u) ↔
      imageCondition p ≤ (historyCompleteEmbed (hcb.trans hba) old hP).toFun u := by
    apply (image_le_historyCompleteEmbed hba old hP p _).trans
    apply (image_le_historyCompleteEmbed hcb (subHistory hba old) (subHistory_persistent hba old hP)
      (historyCutPrefix hba old hP p) u).trans
    have he : historyCutPrefix hcb (subHistory hba old) (subHistory_persistent hba old hP)
        (historyCutPrefix hba old hP p) = historyCutPrefix (hcb.trans hba) old hP p := by
      apply goodPrefix_eq_of_trace930
      change cut (cut p.trace b) c = cut p.trace c
      exact cut_cut_of_le_r75 _ hcb
    exact (Iff.of_eq (congrArg (fun q => imageCondition q ≤ u) he)).trans
      (image_le_historyCompleteEmbed (hcb.trans hba) old hP p u).symm
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

end JSP000930.Negative
