import JSP000933ActualTruncatedDyadicBudget

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameErrorBudget_le_nameBudget_r344 (h : Bool) (k n : ℕ) (a b : ℕ → B) :
    nameErrorBudget h k n a b≤nameBudgetValue h (realBitsName a) (realBitsName b) k n := by
  let E : BudgetExpr (Fin 4) := ⟨h,(SetBitExpr.var 0).symmDiff (.var 1),.const false,k⟩
  let R : BudgetExpr (Fin 4) := ⟨h,.var 0,.var 1,k⟩
  have hG (X : Fin 4 → Set ℕ) : E.groundHolds X n → R.groundHolds X n := by
    intro hE
    apply GroundBudgetHolds.of_diff_subset_r232 h k n _ hE
    intro m hm
    simp [E,R,SetBitExpr.groundSet,SetBitExpr.evalProp,SetBitExpr.symmDiff,
      SetBitExpr.join,Set.mem_sdiff,Set.mem_union,Set.mem_inter_iff] at hm ⊢ <;> tauto
  have hLift := finite_budget_unary_r233 E R (nameFour a b a b) n hG
  unfold nameErrorBudget bitsSymmDiff bitsJoin bitsMeet bitsComplement
  simpa [E,R,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.symmDiff,
    SetBitExpr.evalB_join_r249,SetBitExpr.evalB,nameFour,bitsSymmDiff,bitsJoin,bitsMeet,
    bitsComplement,truthBit,membershipBits_realBitsName_r128] using hLift

theorem localEq_of_eventuallySmallError_r344 (h : Bool) (p : B) (a b : ℕ → B)
    (hE : ∀ k : ℕ, k≠0 → p≤eventuallySmallError h k a b) : LocalEq h p a b := by
  have hOne (u v : ℕ → B) (hU : ∀ k : ℕ, k≠0 → p≤eventuallySmallError h k u v) :
      p≤nameOrderValue h (realBitsName u) (realBitsName v) := by
    apply nameOrder_of_positiveTails_r229
    intro k hk
    apply (hU k hk).trans
    apply iSup_le
    intro N
    apply le_iSup_of_le N
    apply budgetTail_of_forall_r229
    intro n hn
    exact (budgetTail_apply_r229 _ _ _ n hn).trans (nameErrorBudget_le_nameBudget_r344 h k n u v)
  exact ⟨hOne a b hE,hOne b a (fun k hk => (hE k hk).trans_eq (eventuallySmallError_comm_r335 h k a b))⟩

theorem nat_succ_le_power_two_r344 (j : ℕ) : j+1≤(2:ℕ)^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ]
    omega

theorem actualHybrid_harmEq_representative_r344 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) : LocalEq true p (actualHybridBit f x) (R x) := by
  apply localEq_of_eventuallySmallError_r344
  intro k hk
  let J := 4*k
  let H := actualHybridBit f x
  let T := actualTruncatedHybrid f x J
  have hk2 : 2*k≠0 := by omega
  have hJ : 4*k≤(2:ℕ)^J := (Nat.le_succ J).trans (nat_succ_le_power_two_r344 J)
  have hD : (2:ℕ)^J≤dyadicApproxDen J := by
    unfold dyadicApproxDen dyadicGapDen
    rw [pow_succ]
    omega
  have hLeft : p≤eventuallySmallError true (2*k) H T :=
    (actualHybrid_trunc_harmEq_r341 f R hF x J).eventuallySmallError_r290 _ hk2
  have hMiddle : p≤eventuallySmallError true (4*k) T (f J x) :=
    (actualTruncated_smallAllPrefixes_r343 f R hF x J).trans
      ((smallAllPrefixes_le_eventuallySmallError_r290 _ _ _ _).trans
        (eventuallySmallError_scale_antitone_r316 _ _ _ hJ))
  have hRight : p≤eventuallySmallError true (4*k) (f J x) (R x) :=
    (hF J x).trans (eventuallySmallError_scale_antitone_r316 _ _ _ (hJ.trans hD))
  have hM := eventuallySmallError_triangle_r290 true (2*k) T (f J x) (R x)
  rw [show 2*(2*k)=4*k by omega] at hM
  exact (le_inf hLeft ((le_inf hMiddle hRight).trans hM)).trans
    (eventuallySmallError_triangle_r290 true k H T (R x))

end SetLanguage
end JSP000933
