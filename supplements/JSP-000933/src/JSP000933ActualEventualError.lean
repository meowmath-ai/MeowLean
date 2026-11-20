import JSP000933ActualErrorBudgetXor

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def eventualBudgetAt (T : ℕ → ℕ → B) (k : ℕ) : B :=
  ⨆ N : ℕ, budgetTail T k N

theorem eventualBudgetAt_binary_r290 (T S R : ℕ → ℕ → B) (k : ℕ)
    (h : ∀ n, T (2*k) n⊓S (2*k) n≤R k n) :
    eventualBudgetAt T (2*k)⊓eventualBudgetAt S (2*k)≤eventualBudgetAt R k := by
  unfold eventualBudgetAt
  rw [iSup_inf_iSup]
  apply iSup_le
  rintro ⟨N,M⟩
  apply le_iSup_of_le (max N M)
  apply budgetTail_of_forall_r229
  intro n hn
  exact (le_inf
    (inf_le_left.trans (budgetTail_apply_r229 T (2*k) N n ((le_max_left _ _).trans hn)))
    (inf_le_right.trans (budgetTail_apply_r229 S (2*k) M n ((le_max_right _ _).trans hn)))).trans (h n)

noncomputable def eventuallySmallError (h : Bool) (k : ℕ) (x y : ℕ → B) : B :=
  eventualBudgetAt (fun k n => nameErrorBudget h k n x y) k

theorem smallAllPrefixes_le_eventuallySmallError_r290 (h : Bool) (k : ℕ) (a b : ℕ → B) :
    smallAllPrefixes h k (bitsSymmDiff a b)≤eventuallySmallError h k a b := by
  unfold eventuallySmallError eventualBudgetAt
  apply le_iSup_of_le 0
  exact budgetTail_of_forall_r229 _ _ _ _ (fun n _ => iInf_le _ n)

theorem eventuallySmallError_xorPairs_r290 (h : Bool) (k : ℕ) (a b c d : ℕ → B) :
    eventuallySmallError h (2*k) a b⊓eventuallySmallError h (2*k) c d≤
      eventuallySmallError h k (bitsSymmDiff a c) (bitsSymmDiff b d) :=
  eventualBudgetAt_binary_r290 _ _ _ k (nameErrorBudget_xorPairs_r289 h a b c d k)

theorem eventuallySmallError_triangle_r290 (h : Bool) (k : ℕ) (a b c : ℕ → B) :
    eventuallySmallError h (2*k) a b⊓eventuallySmallError h (2*k) b c≤eventuallySmallError h k a c :=
  eventualBudgetAt_binary_r290 _ _ _ k (nameErrorBudget_triangle_r289 h a b c k)

theorem LocalEq.eventuallySmallError_r290 {h : Bool} {p : B} {a b : ℕ → B}
    (he : LocalEq h p a b) (k : ℕ) (hk : k≠0) : p≤eventuallySmallError h k a b := by
  let T := nameBudgetValue h (realBitsName a) (realBitsName b)
  let S := nameBudgetValue h (realBitsName b) (realBitsName a)
  have hk' : 2*k≠0 := Nat.mul_ne_zero (by decide) hk
  have hA : p≤eventualBudgetAt T (2*k) :=
    he.1.trans (nameOrder_positiveTails_r229 h (realBitsName a) (realBitsName b) (2*k) hk')
  have hB : p≤eventualBudgetAt S (2*k) :=
    he.2.trans (nameOrder_positiveTails_r229 h (realBitsName b) (realBitsName a) (2*k) hk')
  exact (le_inf hA hB).trans
    (eventualBudgetAt_binary_r290 T S _ k (nameBudget_twosides_error_r289 h a b k))

end SetLanguage
end JSP000933
