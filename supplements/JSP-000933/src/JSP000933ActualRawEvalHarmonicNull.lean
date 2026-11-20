import JSP000933ActualCommonPrefixWindowError

open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def groundTrimWindowPiece {N : ℕ} (H : ActualStageHistory N) (J n : ℕ)
    (A C : Set ℕ) (i : ℕ) : Set ℕ :=
  if J+i<n then xorSet A C∩(groundStageWindow H (J+i) : Set ℕ) else ∅

theorem actualTrim_singleBudget_r363 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) (hX : p≤bitsBelowValue x (actualSourceUnion T))
    (J n : ℕ) : p≤nameErrorBudget true (2^J) n
      (bitsMeet (actualAfterStageOut T J) (L (actualPaddedInput T x)))
      (bitsMeet (actualAfterStageOut T J) (actualRawOutput T x)) := by
  classical
  let N := max (J+1) (n+2)
  let a := bitsMeet (actualAfterStageOut T J) (L (actualPaddedInput T x))
  let b := bitsMeet (actualAfterStageOut T J) (actualRawOutput T x)
  have hJ : J<N := (Nat.lt_succ_self J).trans_le (le_max_left _ _)
  have hn : n+2≤N := le_max_right _ _
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨H,s,hs,hsq,hS⟩ := exists_nonzero_below_choice_r135 q hq (T.level N).weight
    (hqp.trans_eq (T.level N).covers.symm)
  obtain ⟨A,C,r,hr,hrs,hA,hC⟩ := exists_joint_crispPrefix_r362 a b n s hs
  have hrH := hrs.trans hS
  have hValid : (T.level N).weight H≠⊥ := fun he => hs (le_bot_iff.mp (hS.trans_eq he))
  have hg := T.good_history_r354 H hValid
  have hMissInitial : ∀ m<n, m∈xorSet A C → (historyStage H J).out≤ m := by
    intro m hm he
    by_contra hEarly
    have hCut : r⊓actualAfterStageOut T J m=⊥ := by
      have he := mask_under_r302 hrH (actualAfterStageOut_mask_r361 T H J m hJ)
      simpa only [crispTruth,ite_eq_right hEarly,inf_bot_eq] using he
    have hZero (z : ℕ → B) : r⊓bitsMeet (actualAfterStageOut T J) z m=⊥ := by
      change r⊓(actualAfterStageOut T J m⊓z m)=⊥
      rw [← inf_assoc,hCut,bot_inf_eq]
    have hZA : r⊓a m=⊥ := hZero (L (actualPaddedInput T x))
    have hZC : r⊓b m=⊥ := hZero (actualRawOutput T x)
    have hEq : r⊓crispTruth B (m∈A)=r⊓crispTruth B (m∈C) :=
      (hA m hm).symm.trans (hZA.trans (hZC.symm.trans (hC m hm)))
    have hx := nonzero_mask_crisp_agreement_r333 hr hEq
    simp only [xorSet,Set.mem_union,Set.mem_sdiff] at he
    tauto
  let D := groundTrimWindowPiece H J n A C
  have hCover (m : ℕ) (hm : m<n) (he : m∈xorSet A C) :
      m∈({m | ∃ i<n, m∈D i} : Set ℕ) := by
    have hAnchor := hMissInitial m hm he
    have h0J : (historyStage H 0).out≤(historyStage H J).out := by
      by_cases h0 : J=0
      · rw [h0]
      · exact (hg.out_increases_r354 (Nat.pos_of_ne_zero h0) hJ).le
    obtain ⟨k,hKm,hKW⟩ := hg.window_exists_r357 (by omega) (h0J.trans hAnchor)
    have hJK : J≤k := by
      by_contra hNK
      have hL : k<J := Nat.lt_of_not_ge hNK
      have hOO : (historyStage H (k+1)).out≤(historyStage H J).out := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hL) with het | hlt
        · exact (congrArg (fun i => (historyStage H i).out) het).le
        · exact (hg.out_increases_r354 hlt hJ).le
      exact (not_lt_of_ge (hOO.trans hAnchor)) (Finset.mem_Ico.mp hKW).2
    let i := k-J
    have heq : J+i=k := Nat.add_sub_of_le hJK
    have hi : i<n := (Nat.sub_le k J).trans_lt (hKm.trans_lt hm)
    refine ⟨i,hi,?_⟩
    dsimp only [D]
    rw [groundTrimWindowPiece,heq,ite_eq_left (hKm.trans_lt hm)]
    exact ⟨he,hKW⟩
  have hMass (i : ℕ) (_ : i<n) :
      ((2:ℕ)^i*(2*(2:ℕ)^J))*groundBudgetMass true n (D i)≤groundBudgetDenom true n := by
    have hCoeff : (2:ℕ)^i*(2*(2:ℕ)^J)=dyadicGapDen (J+i) := by
      unfold dyadicGapDen
      rw [pow_succ,pow_add]
      ring
    dsimp only [D]
    rw [hCoeff,groundTrimWindowPiece]
    by_cases hI : J+i<n
    · rw [ite_eq_left hI]
      have hE := actualTrim_groundWindow_error_r362 T H hValid hrH hr x
        (hrs.trans (hsq.trans (hqp.trans hX))) J (J+i) n (Nat.le_add_right J i) (by omega)
        (by omega) hA hC
      rwa [groundBudgetHolds_weighted_r232,Set.sdiff_empty] at hE
    · simp [hI,groundBudgetMass]
  have hGround : GroundBudgetHolds true (xorSet A C) ∅ (2^J) n := by
    rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
    apply (Nat.mul_le_mul_left _ ((groundBudgetMass_prefix_mono_r341 true n hCover).trans
        (groundBudgetMass_finite_union_r343 true n D n))).trans
    exact dyadic_natBudget_sum_r343 (groundBudgetDenom true n) n (2^J) (fun i => groundBudgetMass true n (D i)) hMass
  exact ⟨r,hr,hrs.trans hsq,nameErrorBudget_crispPrefix_complete_r340 true (2^J) n hA hC hGround⟩

theorem actualRawOutput_harmEq_padded_r363 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) (hX : p≤bitsBelowValue x (actualSourceUnion T)) :
    LocalEq true p (L (actualPaddedInput T x)) (actualRawOutput T x) := by
  apply localEq_of_eventuallySmallError_r344
  intro k hk
  let J := 4*k
  let a := L (actualPaddedInput T x)
  let b := actualRawOutput T x
  let aJ := bitsMeet (actualAfterStageOut T J) a
  let bJ := bitsMeet (actualAfterStageOut T J) b
  have hJ : 4*k≤(2:ℕ)^J := (Nat.le_succ J).trans (nat_succ_le_power_two_r344 J)
  have hA : p≤eventuallySmallError true (2*k) a aJ :=
    (actualTrim_output_harmEq_r361 T J a).symm_r236.eventuallySmallError_r290 _ (by omega)
  have hB : p≤eventuallySmallError true (4*k) bJ b :=
    (actualTrim_output_harmEq_r361 T J b).eventuallySmallError_r290 _ (by omega)
  have hPrefixes : p ≤ smallAllPrefixes true (2^J) (bitsSymmDiff aJ bJ) :=
    le_iInf (actualTrim_singleBudget_r363 T x hX J)
  have hM : p≤eventuallySmallError true (4*k) aJ bJ :=
    hPrefixes.trans ((smallAllPrefixes_le_eventuallySmallError_r290 true (2^J) aJ bJ).trans
      (eventuallySmallError_scale_antitone_r316 true aJ bJ hJ))
  have he := eventuallySmallError_triangle_r290 true (2*k) aJ bJ b
  rw [show 2*(2*k)=4*k by omega] at he
  exact (le_inf hA ((le_inf hM hB).trans he)).trans
    (eventuallySmallError_triangle_r290 true k a aJ b)

end SetLanguage
end JSP000933
