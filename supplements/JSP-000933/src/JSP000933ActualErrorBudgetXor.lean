import JSP000933ActualOneSideRegularApproximation
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.Tauto

open scoped Flypitch symmDiff

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def nameErrorBudget (h : Bool) (k n : ℕ) (a b : ℕ → B) : B :=
  nameBudgetValue h (realBitsName (bitsSymmDiff a b)) (realBitsName (fun _ => ⊥)) k n

def nameFour (a b c d : ℕ → B) (i : Fin 4) : bSet B :=
  realBitsName (if i=0 then a else if i=1 then b else if i=2 then c else d)

theorem nameErrorBudget_xorPairs_r289 (h : Bool) (a b c d : ℕ → B) (k n : ℕ) :
    nameErrorBudget h (2*k) n a b⊓nameErrorBudget h (2*k) n c d≤
      nameErrorBudget h k n (bitsSymmDiff a c) (bitsSymmDiff b d) := by
  let e : SetBitExpr (Fin 4) := (SetBitExpr.var 0).symmDiff (.var 1)
  let f : SetBitExpr (Fin 4) := (SetBitExpr.var 2).symmDiff (.var 3)
  let z : SetBitExpr (Fin 4) := ((SetBitExpr.var 0).symmDiff (.var 2)).symmDiff ((SetBitExpr.var 1).symmDiff (.var 3))
  let E : BudgetExpr (Fin 4) := ⟨h,e,.const false,2*k⟩
  let F : BudgetExpr (Fin 4) := ⟨h,f,.const false,2*k⟩
  let R : BudgetExpr (Fin 4) := ⟨h,z,.const false,k⟩
  have hh (x : Fin 4 → Set ℕ) : E.groundHolds x n → F.groundHolds x n → R.groundHolds x n := by
    intro hE hF
    apply GroundBudgetHolds.of_diff_cover_r232 h k n _ hE hF
    intro m hm
    simp [E,F,R,e,f,z,SetBitExpr.groundSet,SetBitExpr.evalProp,SetBitExpr.symmDiff,
      SetBitExpr.join,Set.mem_sdiff,Set.mem_union,Set.mem_inter_iff] at hm ⊢ <;> tauto
  have hLift := finite_budget_binary_r233 E F R (nameFour a b c d) n hh
  unfold nameErrorBudget bitsSymmDiff bitsJoin bitsMeet bitsComplement
  simpa [E,F,R,e,f,z,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.symmDiff,
    SetBitExpr.evalB_join_r249,SetBitExpr.evalB,nameFour,bitsSymmDiff,bitsJoin,bitsMeet,
    bitsComplement,truthBit,membershipBits_realBitsName_r128] using hLift

theorem bitsSymmDiff_symmDiff_cancel_r289 (a b c : ℕ → B) :
    bitsSymmDiff (bitsSymmDiff a b) (bitsSymmDiff b c)=bitsSymmDiff a c := by
  funext m
  have hA (x y : ℕ → B) : bitsSymmDiff x y m=x m ∆ y m := by
    simp only [bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement,symmDiff_def,sdiff_eq,inf_comm (y m) (x m)ᶜ]
  simp only [hA, symmDiff_assoc, symmDiff_symmDiff_cancel_left]

theorem nameErrorBudget_triangle_r289 (h : Bool) (a b c : ℕ → B) (k n : ℕ) :
    nameErrorBudget h (2*k) n a b⊓nameErrorBudget h (2*k) n b c≤nameErrorBudget h k n a c := by
  have H := nameErrorBudget_xorPairs_r289 h a b b c k n
  unfold nameErrorBudget at H ⊢
  rw [bitsSymmDiff_symmDiff_cancel_r289] at H
  exact H

theorem nameBudget_twosides_error_r289 (h : Bool) (a b : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName a) (realBitsName b) (2*k) n⊓
      nameBudgetValue h (realBitsName b) (realBitsName a) (2*k) n≤nameErrorBudget h k n a b := by
  let E : BudgetExpr (Fin 4) := ⟨h,.var 0,.var 1,2*k⟩
  let F : BudgetExpr (Fin 4) := ⟨h,.var 1,.var 0,2*k⟩
  let R : BudgetExpr (Fin 4) := ⟨h,(SetBitExpr.var 0).symmDiff (.var 1),.const false,k⟩
  have hh (x : Fin 4 → Set ℕ) : E.groundHolds x n → F.groundHolds x n → R.groundHolds x n := by
    intro hE hF
    apply GroundBudgetHolds.of_diff_cover_r232 h k n _ hE hF
    intro m hm
    simp [E,F,R,SetBitExpr.groundSet,SetBitExpr.evalProp,SetBitExpr.symmDiff,
      SetBitExpr.join,Set.mem_sdiff,Set.mem_union,Set.mem_inter_iff] at hm ⊢ <;> tauto
  have hLift := finite_budget_binary_r233 E F R (nameFour a b a b) n hh
  unfold nameErrorBudget bitsSymmDiff bitsJoin bitsMeet bitsComplement
  simpa [E,F,R,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.symmDiff,
    SetBitExpr.evalB_join_r249,SetBitExpr.evalB,nameFour,bitsSymmDiff,bitsJoin,bitsMeet,
    bitsComplement,truthBit,membershipBits_realBitsName_r128] using hLift

end SetLanguage
end JSP000933
