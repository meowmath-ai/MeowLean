import JSP000933PastOnlyRealDecoder

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

theorem orderIsoReduction_leftInverse_r161 {P Q : Type} [Preorder P] [Preorder Q] (e : P ≃o Q)
    (U : RO P) : (orderIsoReduction e).boolPullback ((orderIsoReduction e.symm).boolPullback U) = U := by
  apply Heyting.Regular.coe_injective
  ext p
  change e.symm (e p) ∈ (U : LowerSet P) ↔ p ∈ (U : LowerSet P)
  rw [OrderIso.symm_apply_apply]

noncomputable def actualHistoryEnum (policy : StagePolicy OmegaTwoIndex OCALabel)
    (hBefore : ∀ a, HasCountableAntichains (Before (iterationRules policy) a))
    (CH : (𝔠 : Cardinal) = ℵ₁)
    (a : OmegaTwoIndex) (i : OmegaOneIndex) (n : ℕ) : RO (Before (iterationRules policy) a) :=
  let F := orderIsoReduction (prefixOrderIso_r85 policy a)
  let hCCC := BooleanCCC_of_completeValueMap_r158 F.completeValueMap
    (booleanCCC_of_conditionCCC_r66 (hBefore a))
  F.boolPullback (historyEnum a (earlierValidated policy a) hCCC CH i n)

theorem actualHistoryEnum_surj_r161 (policy : StagePolicy OmegaTwoIndex OCALabel)
    (hBefore : ∀ a, HasCountableAntichains (Before (iterationRules policy) a))
    (CH : (𝔠 : Cardinal) = ℵ₁) (a : OmegaTwoIndex) :
    Function.Surjective (actualHistoryEnum policy hBefore CH a) := by
  intro x
  let e := prefixOrderIso_r85 policy a
  let inv (n : ℕ) := (orderIsoReduction e.symm).boolPullback (x n)
  have hCCC := BooleanCCC_of_completeValueMap_r158 (orderIsoReduction e).completeValueMap
    (booleanCCC_of_conditionCCC_r66 (hBefore a))
  obtain ⟨i,hi⟩ := historyEnum_surjective_r160 a (earlierValidated policy a) hCCC CH inv
  refine ⟨i,funext (fun n => ?_)⟩
  change (orderIsoReduction e).boolPullback (historyEnum a (earlierValidated policy a) hCCC CH i n) = x n
  rw [congrFun hi n]
  exact orderIsoReduction_leftInverse_r161 e (x n)

theorem historyRealDecode_actual_r161 (policy : StagePolicy OmegaTwoIndex OCALabel)
    (hBefore : ∀ a, HasCountableAntichains (Before (iterationRules policy) a))
    (CH : (𝔠 : Cardinal) = ℵ₁)
    (code : OmegaTwoIndex × OmegaOneIndex ↪ OmegaTwoIndex) (a j : OmegaTwoIndex)
    (hPersist : HistoryPersistent (earlierValidated policy a))
    (hCCC : BooleanCCC (RO (GoodPrefix (earlierValidated policy a)))) (n : ℕ) :
    (orderIsoReduction (prefixOrderIso_r85 policy a)).boolPullback
      (historyRealDecode code a (earlierValidated policy a) hPersist hCCC CH j n) =
    canonicalStageDecode code (actualHistoryEnum policy hBefore CH) a j n := by
  classical
  by_cases h : ∃ q : {q : OmegaTwoIndex × OmegaOneIndex // q.1 < a}, code q.1 = j
  · simp only [historyRealDecode,canonicalStageDecode,dite_eq_left h,actualHistoryEnum]
    exact historyRestriction_actual_value_r158 policy (Classical.choose h).2.le _
  · simp only [historyRealDecode,canonicalStageDecode,dite_eq_right h,RestrictionMap.boolPullback_bot_r91]

end FiniteSupport
end JSP000933
