import JSP000933ActualDisjointOverlapBudget

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_decided_blockInput_r374 {k : ℕ} (H : ActualStageHistory (k+2)) (x : ℕ → B) (q : B) (hq : q≠⊥) :
    ∃ (a : BlockInput H) (r : B), r≠⊥ ∧ r≤q ∧
      ∀ m∈blockSnapshotSource H, r⊓x m=r⊓crispFinsetBits a.val m := by
  classical
  let S := blockSnapshotSource H
  let N := S.sup id+1
  obtain ⟨A,_,r,hr,hrq,hA,_⟩ := exists_joint_crispPrefix_r362 x x N q hq
  let a : BlockInput H := ⟨S.filter (fun m => m∈A),Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  refine ⟨a,r,hr,hrq,?_⟩
  intro m hm
  have hN : m<N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  have hmS : m ∈ S := hm
  have he : (m∈A) ↔ m∈a.val := by simp only [a,Finset.mem_filter,hmS,true_and]
  exact (hA m hN).trans (congrArg (fun b : B => r⊓b) (crispTruth_propext_r188 he))

theorem groundBudget_empty_before_piece_r374 (h : Bool) (k n : ℕ) (D : Finset ℕ)
    (hD : ∀ m∈D, n≤ m) : GroundBudgetHolds h (D : Set ℕ) ∅ k n := by
  classical
  rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
  have he : groundBudgetMass h n (D : Set ℕ)=0 := by
    unfold groundBudgetMass
    apply Finset.sum_eq_zero
    intro m hm
    have hn : m∉(D : Set ℕ) := fun h => not_lt_of_ge (hD m h) (Finset.mem_range.mp hm)
    simp [hn]
  simp [he]

theorem groundAllBudgets_from_namedTail_r374 {q : B} (hq : q≠⊥)
    (h : Bool) (k N : ℕ) (a : ℕ → B) (D : Finset ℕ)
    (hD : ∀ m∈D, q≤a m) (hN : ∀ m∈D, N≤ m)
    (hT : q≤budgetTail (nameBudgetValue h (realBitsName a) (realBitsName (fun _ => ⊥))) k N) :
    GroundAllBudgets h k D := by
  intro n
  by_cases hn : N≤n
  · exact groundBudget_from_namedContaining_r370 hq h k n a D hD
      (hT.trans (budgetTail_apply_r229 _ k N n hn))
  · exact groundBudget_empty_before_piece_r374 h k n D (fun m hm => (Nat.le_of_not_ge hn).trans (hN m hm))

theorem actualXorNull_of_localEq_r374 {p : B} {a b : ℕ → B} (h : LocalEq true p a b) :
    LocalLE true p (bitsSymmDiff a b) (fun _ => ⊥) := by
  have hX := h.xor_congr_r346 (LocalEq.refl_r239 true p b)
  have he : bitsSymmDiff b b=(fun _ => ⊥) := by
    funext m
    rw [bitsSymmDiff_at_r298,symmDiff_self]
  rw [he] at hX
  exact hX.1

end SetLanguage
end JSP000933
