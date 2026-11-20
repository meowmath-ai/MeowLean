import JSP000933ActualGroundPrefixBudgets

open scoped Flypitch BigOperators

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem groundBudgetMass_prefix_mono_r341 (h : Bool) (n : ℕ) {A C : Set ℕ}
    (hAC : ∀ m<n, m∈A → m∈C) : groundBudgetMass h n A≤groundBudgetMass h n C := by
  classical
  unfold groundBudgetMass
  apply Finset.sum_le_sum
  intro m hm
  by_cases hM : m∈A
  · simp [hM,hAC m (Finset.mem_range.mp hm) hM]
  · simp [hM]

theorem groundHarmBudget_late_agreement_r341 (A C : Set ℕ) (N k n : ℕ)
    (hN : GroundBudgetHolds true (Set.Iio N) ∅ k n)
    (hE : ∀ m<n, N≤ m → (m∈A ↔ m∈C)) : GroundBudgetHolds true A C k n := by
  rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty] at hN
  rw [groundBudgetHolds_weighted_r232]
  apply (Nat.mul_le_mul_left k (groundBudgetMass_prefix_mono_r341 true n ?_)).trans hN
  intro m hm hM
  exact Nat.lt_of_not_ge (fun h => hM.2 ((hE m hm h).mp hM.1))

theorem actualHarBudget_late_agreement_r341 {p : B} (a b : ℕ → B) (N k n : ℕ)
    (hN : GroundBudgetHolds true (Set.Iio N) ∅ k n)
    (h : ∀ m≥N, p⊓a m=p⊓b m) :
    p≤nameBudgetValue true (realBitsName a) (realBitsName b) k n := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨A,C,r,hr,hrq,hA,hC⟩ := exists_joint_ground_prefix_r211 (realBitsName a) (realBitsName b) n q hq
  have hEq (m : ℕ) (hm : m<n) (hN' : N≤ m) : m∈A ↔ m∈C := by
    have hL := hA m hm
    have hR := hC m hm
    have hSame : r⊓a m=r⊓b m := mask_under_r302 (hrq.trans hqp) (h m hN')
    rw [membershipBits_realBitsName_r128] at hL hR
    change r⊓a m=r⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B A) at hL
    change r⊓b m=r⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B C) at hR
    rw [checkedNat_ground_mem_r197] at hL hR
    exact nonzero_mask_crisp_agreement_r333 hr (hL.symm.trans (hSame.trans hR))
  have hG : r≤nameBudgetValue true (groundSubsetName B A) (groundSubsetName B C) k n := by
    rw [nameBudgetValue_ground_r226,crispTruth,ite_eq_left (groundHarmBudget_late_agreement_r341 A C N k n hN hEq)]
    exact le_top
  have hM := nameBudgetValue_mask_r226 hA hC true k
  exact ⟨r,hr,hrq,((le_inf le_rfl hG).trans_eq hM.symm).trans inf_le_right⟩

theorem harmonicLocalEq_late_agreement_r341 {p : B} (a b : ℕ → B) (N : ℕ)
    (h : ∀ m≥N, p⊓a m=p⊓b m) : LocalEq true p a b := by
  have hOne (u v : ℕ → B) (he : ∀ m≥N, p⊓u m=p⊓v m) :
      p≤nameOrderValue true (realBitsName u) (realBitsName v) := by
    apply nameOrder_of_positiveTails_r229
    intro k hk
    obtain ⟨M,hM⟩ := groundHarmBudget_initialSegment_eventual_r339 N k hk
    exact le_iSup_of_le M (budgetTail_of_forall_r229 _ k M p (fun n hn =>
      actualHarBudget_late_agreement_r341 u v N k n (hM n hn) he))
  exact ⟨hOne a b h,hOne b a (fun m hm => (h m hm).symm)⟩

theorem actualHybrid_trunc_harmEq_r341 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (J : ℕ) : LocalEq true p (actualHybridBit f x) (actualTruncatedHybrid f x J) := by
  let U := fun M => actualRecursiveCutLE (actualDyadicGapTail f x) J M
  let T := liveLE true (actualHybridBit f x) (actualTruncatedHybrid f x J) ⊓
    liveLE true (actualTruncatedHybrid f x J) (actualHybridBit f x)
  have hP : p≤⨆ M, U M := actualRecursiveCutLE_eventually_r338 f R hF x J
  have hpT : p≤T := by
    apply (show p≤p⊓(⨆ M, U M) from le_inf le_rfl hP).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro M
    have he := harmonicLocalEq_late_agreement_r341 (p := p⊓U M) _ _ M
      (actualHybrid_agrees_trunc_late_r338 f x J M inf_le_right)
    exact le_inf he.1 he.2
  exact ⟨hpT.trans inf_le_left,hpT.trans inf_le_right⟩

end SetLanguage
end JSP000933
