import JSP000933InternalCCCSelection

namespace JSP000933
namespace BooleanCompletion

open OpenGraphForcing

theorem BooleanCCC_of_completeValueMap_r158 {B C : Type}
    [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
    (F : CompleteValueMap B C) (hCCC : BooleanCCC C) : BooleanCCC B := by
  classical
  intro S hN hDis
  have hc : (F.toFun '' S).Countable := by
    apply hCCC
    · rintro _ ⟨b,hb,rfl⟩ h
      exact hN b hb (F.injective (h.trans F.map_bot.symm))
    · rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩ hne
      apply disjoint_iff_inf_le.mpr
      rw [← F.map_inf]
      exact (F.monotone (disjoint_iff_inf_le.mp (hDis b hb c hc (fun he => hne (congrArg F.toFun he))))).trans_eq
        F.map_bot
  exact Set.countable_of_injective_of_countable_image F.injective.injOn hc

end BooleanCompletion

namespace FiniteSupport

open BooleanCompletion

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T]

theorem goodPrefix_trace_injective_r158 {a : A} (old : PrefixValidator a T) :
    Function.Injective (GoodPrefix.trace : GoodPrefix old → LabelTrace A T) := by
  rintro ⟨p,hpF,hpB,hpV⟩ ⟨q,hqF,hqB,hqV⟩ h
  change p = q at h
  cases h
  rfl

theorem historyRestriction_actual_cut_r158 (policy : StagePolicy A T) {a b : A} (h : b ≤ a)
    (p : Before (iterationRules policy) a) :
    (historyRestriction h (earlierValidated policy a)
      (earlierHistory_persistent_r131 policy a)).toFun ((prefixOrderIso_r85 policy a) p) =
        (prefixOrderIso_r85 policy b) (restrict p.1 b) := by
  apply goodPrefix_trace_injective_r158
  exact historyRestriction_trace_r132 h _ _ _

theorem historyRestriction_actual_value_r158 (policy : StagePolicy A T) {a b : A} (h : b ≤ a)
    (U : RO (GoodPrefix (earlierValidated policy b))) :
    (orderIsoReduction (prefixOrderIso_r85 policy a)).boolPullback
      ((historyRestriction h (earlierValidated policy a)
        (earlierHistory_persistent_r131 policy a)).boolPullback U) =
    (prefixReduction (R := iterationRules policy) h).boolPullback
      ((orderIsoReduction (prefixOrderIso_r85 policy b)).boolPullback U) := by
  apply Heyting.Regular.coe_injective
  ext p
  change ((historyRestriction h (earlierValidated policy a)
    (earlierHistory_persistent_r131 policy a)).toFun ((prefixOrderIso_r85 policy a) p) ∈
      (↑U : LowerSet (GoodPrefix (earlierValidated policy b)))) ↔
    ((prefixOrderIso_r85 policy b) (restrict p.1 b) ∈ (↑U : LowerSet (GoodPrefix (earlierValidated policy b))))
  rw [historyRestriction_actual_cut_r158]
  rfl

end FiniteSupport
end JSP000933
