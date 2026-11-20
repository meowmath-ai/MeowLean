import JSP000933ActualWholeBlockPseudointersection

open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem groundBudgetHolds_late_agreement_r333 (a b : Set ℕ) (N k n : ℕ)
    (hn : k*N≤n) (h : ∀ m<n, N≤ m → (m∈a ↔ m∈b)) :
    GroundBudgetHolds false a b k n := by
  classical
  rw [groundBudgetHolds_weighted_r232]
  have hW : groundBudgetMass false n (a \ b)≤N := by
    unfold groundBudgetMass
    refine (Finset.sum_le_sum (g := fun i => if i<N then 1 else 0) ?_).trans ?_
    · intro m hm
      by_cases hM : m<N
      · by_cases he : m∈a \ b <;> simp [hM,he,groundBudgetWeight]
      · have hnM : m∉a \ b := fun he => he.2 ((h m (Finset.mem_range.mp hm)
          (Nat.le_of_not_gt hM)).mp he.1)
        simp [hM,hnM,groundBudgetWeight]
    · have he : (∑ i ∈ Finset.range n, if i<N then 1 else 0) =
          ((Finset.range n).filter (fun i => i<N)).card := by
        rw [← Finset.sum_filter]
        simp
      rw [he]
      simpa only [Finset.card_range] using (Finset.card_le_card
        (show (Finset.range n).filter (fun i => i<N) ⊆ Finset.range N from
          fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2))
  have hDenom : groundBudgetDenom false n=n := by simp [groundBudgetDenom,groundBudgetWeight]
  rw [hDenom]
  exact (Nat.mul_le_mul_left k hW).trans hn

theorem nonzero_mask_crisp_agreement_r333 {p : B} (hp : p≠⊥) {a b : Prop}
    (h : p⊓crispTruth B a=p⊓crispTruth B b) : a↔b := by
  classical
  constructor
  · intro ha
    by_contra hb
    exact hp (by simpa [crispTruth,ha,hb] using h)
  · intro hb
    by_contra ha
    exact hp (by simpa [crispTruth,ha,hb] using h.symm)

theorem actualOrdBudget_late_agreement_r333 {p : B} (a b : ℕ → B) (N k n : ℕ)
    (hn : k*N≤n) (h : ∀ m≥N, p⊓a m=p⊓b m) :
    p≤nameBudgetValue false (realBitsName a) (realBitsName b) k n := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨A,C,r,hr,hrq,hA,hC⟩ := exists_joint_ground_prefix_r211 (realBitsName a) (realBitsName b) n q hq
  have hEq (m : ℕ) (hm : m<n) (hN : N≤ m) : m∈A ↔ m∈C := by
    have hL := hA m hm
    have hR := hC m hm
    have hSame : r⊓a m=r⊓b m := mask_under_r302 (hrq.trans hqp) (h m hN)
    rw [membershipBits_realBitsName_r128] at hL hR
    change r⊓a m=r⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B A) at hL
    change r⊓b m=r⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B C) at hR
    rw [checkedNat_ground_mem_r197] at hL hR
    exact nonzero_mask_crisp_agreement_r333 hr (hL.symm.trans (hSame.trans hR))
  have hG : r≤nameBudgetValue false (groundSubsetName B A) (groundSubsetName B C) k n := by
    rw [nameBudgetValue_ground_r226,crispTruth,ite_eq_left (groundBudgetHolds_late_agreement_r333 A C N k n hn hEq)]
    exact le_top
  have hM := nameBudgetValue_mask_r226 hA hC false k
  exact ⟨r,hr,hrq,((le_inf le_rfl hG).trans_eq hM.symm).trans inf_le_right⟩

theorem ordinaryLocalEq_late_agreement_r333 {p : B} (a b : ℕ → B) (N : ℕ)
    (h : ∀ m≥N, p⊓a m=p⊓b m) : LocalEq false p a b := by
  constructor
  · apply nameOrder_of_positiveTails_r229
    intro k _
    exact le_iSup_of_le (k*N) (budgetTail_of_forall_r229 _ _ _ _ (fun n hn =>
      actualOrdBudget_late_agreement_r333 a b N k n hn h))
  · apply nameOrder_of_positiveTails_r229
    intro k _
    exact le_iSup_of_le (k*N) (budgetTail_of_forall_r229 _ _ _ _ (fun n hn =>
      actualOrdBudget_late_agreement_r333 b a N k n hn (fun i hi => (h i hi).symm)))

end SetLanguage
end JSP000933
