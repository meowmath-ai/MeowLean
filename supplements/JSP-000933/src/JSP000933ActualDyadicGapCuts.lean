import JSP000933ActualSameCapDyadicUniform

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def dyadicGapDen (j : ℕ) : ℕ := 2^(j+1)
def dyadicApproxDen (j : ℕ) : ℕ := 2*dyadicGapDen j

theorem dyadicGapDen_pos_r335 (j : ℕ) : 0<dyadicGapDen j := pow_pos (by decide) _
theorem dyadicApproxDen_pos_r335 (j : ℕ) : 0<dyadicApproxDen j := Nat.mul_pos (by decide) (dyadicGapDen_pos_r335 j)

theorem dyadicGapDen_succ_r335 (j : ℕ) : dyadicGapDen (j+1)=2*dyadicGapDen j :=
  (pow_succ (2 : ℕ) (j+1)).trans (Nat.mul_comm _ _)

theorem dyadicApproxDen_mono_succ_r335 (j : ℕ) : dyadicApproxDen j≤dyadicApproxDen (j+1) := by
  unfold dyadicApproxDen
  rw [dyadicGapDen_succ_r335 j]
  omega

theorem eventuallySmallError_comm_r335 (h : Bool) (k : ℕ) (a b : ℕ → B) :
    eventuallySmallError h k a b=eventuallySmallError h k b a :=
  congrArg (fun e => eventualBudgetAt (fun k n => nameBudgetValue h (realBitsName e)
    (realBitsName (fun _ => ⊥)) k n) k) (bitsSymmDiff_comm_r316 a b)

noncomputable def actualDyadicGapTail (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B)
    (j N : ℕ) : B :=
  budgetTail (fun k n => nameErrorBudget true k n (f j x) (f (j+1) x)) (dyadicGapDen j) N

theorem actualDyadicGapTail_mono_r335 (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (j : ℕ) :
    Monotone (actualDyadicGapTail f x j) := by
  intro N M h
  apply budgetTail_of_forall_r229
  intro n hn
  exact budgetTail_apply_r229 _ _ _ _ (h.trans hn)

theorem actualDyadicGapTail_exists_r335 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (j : ℕ) : p≤⨆ N, actualDyadicGapTail f x j N := by
  have hS := (hF (j+1) x).trans
    (eventuallySmallError_scale_antitone_r316 true (f (j+1) x) (R x) (dyadicApproxDen_mono_succ_r335 j))
  have hT := hS.trans_eq (eventuallySmallError_comm_r335 true (dyadicApproxDen j) (f (j+1) x) (R x))
  exact (le_inf (hF j x) hT).trans
    (eventuallySmallError_triangle_r290 true (dyadicGapDen j) (f j x) (R x) (f (j+1) x))

def actualRecursiveCutLE (G : ℕ → ℕ → B) : ℕ → ℕ → B
  | 0, _ => ⊤
  | _+1, 0 => ⊥
  | j+1, m+1 => actualRecursiveCutLE G j m⊓G j (m+1)

theorem actualRecursiveCutLE_mono_r335 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j)) (j : ℕ) :
    Monotone (actualRecursiveCutLE G j) := by
  induction j with
  | zero =>
    intro a b h
    exact le_rfl
  | succ j ih =>
    intro n m h
    cases n with
    | zero => exact bot_le
    | succ n =>
      cases m with
      | zero => omega
      | succ m =>
        exact inf_le_inf (ih (Nat.le_of_succ_le_succ h)) (hG j h)

theorem actualRecursiveCutLE_step_r335 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j)) (j m : ℕ) :
    actualRecursiveCutLE G (j+1) m≤actualRecursiveCutLE G j m := by
  cases m with
  | zero => exact bot_le
  | succ m => exact inf_le_left.trans (actualRecursiveCutLE_mono_r335 G hG j (Nat.le_succ m))

theorem actualRecursiveCutLE_bot_r335 (G : ℕ → ℕ → B) (j m : ℕ) (h : m<j) :
    actualRecursiveCutLE G j m=⊥ := by
  induction j generalizing m with
  | zero => omega
  | succ j ih =>
    cases m with
    | zero => rfl
    | succ m =>
      change actualRecursiveCutLE G j m⊓G j (m+1)=⊥
      rw [ih m (Nat.lt_of_succ_lt_succ h),bot_inf_eq]

noncomputable def actualHybridBit (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (m : ℕ) : B :=
  ⨆ j : ℕ, (actualRecursiveCutLE (actualDyadicGapTail f x) j m⊓
    (actualRecursiveCutLE (actualDyadicGapTail f x) (j+1) m)ᶜ)⊓f j x m

end SetLanguage
end JSP000933
