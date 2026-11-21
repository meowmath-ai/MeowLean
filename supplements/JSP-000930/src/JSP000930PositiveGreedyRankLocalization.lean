import JSP000930PositiveActualCohenContinuum
import JSP000933RelativeGreedyCuts

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.CantorCodes

variable {B N I : Type} [CompleteBooleanAlgebra B] [LinearOrder I] [WellFoundedLT I]

noncomputable def greedyRankWeight (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (rank : N → OmegaOneIndex) (x : TotalBA Q) (i : OmegaOneIndex) (t : N) : B := by
  classical
  exact ⨆ j : I, if rank t = i then greedyTraceWeight Q E x j t else ⊥

theorem greedyRankWeight_bounds (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (hQ : ForcesRelativeCCC Q)
    (rank : N → OmegaOneIndex) (x : TotalBA Q) :
    unboundedValue (fun i => ⨆ t,greedyRankWeight Q E rank x i t) = ⊥ := by
  classical
  apply hQ
  · intro i t
    unfold greedyRankWeight
    apply iSup_le
    intro j
    by_cases ht : rank t = i
    · simpa only [ite_eq_left ht] using greedyTraceWeight_valid_r465 Q E x j t
    · simp only [ite_eq_right ht,bot_le]
  · intro i l hil t u
    apply le_bot_iff.mp
    unfold greedyRankWeight
    rw [iSup_inf_iSup, iSup_inf_eq]
    apply iSup_le
    rintro ⟨j,k⟩
    by_cases ht : rank t = i
    · by_cases hu : rank u = l
      · simp only [ite_eq_left ht,ite_eq_left hu]
        rcases lt_trichotomy j k with hjk | he | hkj
        · exact (greedyTraceWeight_apart_r465 Q E x j k hjk t u).le
        · subst k
          have htu : t ≠ u := fun h => hil.ne (ht.symm.trans ((congrArg rank h).trans hu))
          have hd := ((E.rowApart j htu).mono_left
            (greedyTraceWeight_cell_r465 Q E x j t)).mono_right
              (greedyTraceWeight_cell_r465 Q E x j u)
          exact inf_le_left.trans (disjoint_iff_inf_le.mp hd)
        · rw [inf_comm (greedyTraceWeight Q E x j t) (greedyTraceWeight Q E x k u),
            commonRefinementValue_comm_r464 Q t u]
          exact (greedyTraceWeight_apart_r465 Q E x k j hkj u t).le
      · simp only [ite_eq_right hu,inf_bot_eq,bot_inf_eq,bot_le]
    · simp only [ite_eq_right ht,bot_inf_eq,bot_le]

theorem exists_local_greedy_rank_bound (Q : ValuedPoset B N)
    (E : MixedEnumeration I N B) (hQ : ForcesRelativeCCC Q)
    (hB : BoundsCountableOmegaOneNames B) (rank : N → OmegaOneIndex)
    (x : ℕ → TotalBA Q) (m : B) (hm : m ≠ ⊥) :
    ∃ (c : OmegaOneIndex) (b : B), b ≠ ⊥ ∧ b ≤ m ∧
      ∀ n j t, c ≤ rank t → Disjoint b (greedyTraceWeight Q E (x n) j t) := by
  classical
  let W (n : ℕ) (i : OmegaOneIndex) := ⨆ t,greedyRankWeight Q E rank (x n) i t
  let U (n : ℕ) (b : OmegaOneIndex) := (aboveValue (W n) b)ᶜ
  have hU (n : ℕ) : (⨆ b,U n b) = ⊤ := by
    have h := congrArg (fun a : B => aᶜ) (greedyRankWeight_bounds Q E hQ rank (x n))
    simpa only [unboundedValue,compl_iInf,compl_bot,W,U] using h
  let C (c : OmegaOneIndex) : B := ⨅ n,⨆ b : ↥(Set.Iio c),U n b.val
  have hC : (⨆ c,C c) = ⊤ := by
    apply top_unique
    exact (le_iInf (fun n => (hU n).ge)).trans (hB U)
  have hM : m ≤ ⨆ c,C c := hC.symm ▸ le_top
  obtain ⟨c,b,hb,hbm,hbc⟩ := exists_nonzero_below_choice_r135 m hm C hM
  refine ⟨c,b,hb,hbm,fun n j t ht => ?_⟩
  apply le_compl_iff_disjoint_right.mp
  apply (hbc.trans (iInf_le _ n)).trans
  apply iSup_le
  intro i
  apply compl_le_compl
  unfold aboveValue
  apply le_iSup_of_le (⟨rank t,i.property.trans_le ht⟩ : {a : OmegaOneIndex // i.val < a})
  apply le_iSup_of_le t
  unfold greedyRankWeight
  apply le_iSup_of_le j
  simp only [ite_true]
  exact le_rfl

end JSP000930.Positive
