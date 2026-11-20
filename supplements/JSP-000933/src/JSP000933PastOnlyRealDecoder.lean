import JSP000933HistoryDiamondTags

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing CantorCodes

abbrev OCALabel := ReverseLabels OmegaOneIndex

theorem mk_goodCliquePrefix_le_r160 (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel) :
    Cardinal.mk (GoodPrefix old) ≤ ℵ₁ :=
  mk_GoodPrefix_le_alephOne_r97 (V := old) (mk_omegaTwo_properPrefix_le_alephOne_r97 a)
    mk_groundCliqueLabels_r97.le

noncomputable def historyEnum (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel)
    (hCCC : BooleanCCC (RO (GoodPrefix old))) (CH : (𝔠 : Cardinal) = ℵ₁) :
    OmegaOneIndex → ℕ → RO (GoodPrefix old) :=
  Classical.choose (exists_omegaOneEnumeration_of_bits_r99 hCCC (mk_goodCliquePrefix_le_r160 a old) CH)

theorem historyEnum_surjective_r160 (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel)
    (hCCC : BooleanCCC (RO (GoodPrefix old))) (CH : (𝔠 : Cardinal) = ℵ₁) :
    Function.Surjective (historyEnum a old hCCC CH) :=
  Classical.choose_spec (exists_omegaOneEnumeration_of_bits_r99 hCCC
    (mk_goodCliquePrefix_le_r160 a old) CH)

noncomputable def historyRealDecode (nameCode : OmegaTwoIndex × OmegaOneIndex ↪ OmegaTwoIndex)
    (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel) (hPersist : HistoryPersistent old)
    (hCCC : BooleanCCC (RO (GoodPrefix old))) (CH : (𝔠 : Cardinal) = ℵ₁)
    (j : OmegaTwoIndex) : ℕ → RO (GoodPrefix old) := by
  classical
  exact if h : ∃ q : {q : OmegaTwoIndex × OmegaOneIndex // q.1 < a}, nameCode q.1 = j then
    let q := Classical.choose h
    let F := historyRestriction q.2.le old hPersist
    let earlierCCC := BooleanCCC_of_completeValueMap_r158 F.completeValueMap hCCC
    fun n => F.boolPullback (historyEnum q.1.1 (subHistory q.2.le old) earlierCCC CH q.1.2 n)
  else fun _ => ⊥

theorem historyDomain_actual_r160 (policy : StagePolicy OmegaTwoIndex OCALabel)
    (E : DiamondEncoder OCALabel) (a : OmegaTwoIndex) (G : Set OmegaTwoIndex)
    (j : OmegaTwoIndex) :
    (orderIsoReduction (prefixOrderIso_r85 policy a)).boolPullback
      (historyDomain (old := earlierValidated policy a) E G j) =
      guessDomain (R := iterationRules policy) E a G j := by
  let e := prefixOrderIso_r85 policy a
  let F := orderIsoReduction e
  unfold historyDomain guessDomain
  change F.boolPullback (⨆ q : {q : GoodPrefix (earlierValidated policy a) //
      E.domainTag j (goodTraceCode E q) ∈ G}, imageCondition q.1) =
    ⨆ q : {q : Before (iterationRules policy) a //
      E.domainTag j (E.conditionCode q.1) ∈ G}, imageCondition q.1
  rw [F.boolPullback_iSup_r91]
  apply le_antisymm
  · apply iSup_le
    intro q
    rw [orderIsoReduction_basic_r122]
    have h : goodTraceCode E q.1 = E.conditionCode (e.symm q.1).1 := by
      simpa only [e,OrderIso.apply_symm_apply] using goodTraceCode_actual_r159 policy E (e.symm q.1)
    exact le_iSup_of_le
      (⟨e.symm q.1,by simpa only [h] using q.2⟩ :
        {q : Before (iterationRules policy) a // E.domainTag j (E.conditionCode q.1) ∈ G})
      le_rfl
  · apply iSup_le
    intro q
    have h : E.domainTag j (goodTraceCode E (e q.1)) ∈ G := by
      simpa only [e,goodTraceCode_actual_r159] using q.2
    apply le_iSup_of_le
      (⟨e q.1,h⟩ : {q : GoodPrefix (earlierValidated policy a) // E.domainTag j (goodTraceCode E q) ∈ G})
    rw [orderIsoReduction_basic_r122,OrderIso.symm_apply_apply] <;> exact le_rfl

end FiniteSupport
end JSP000933
