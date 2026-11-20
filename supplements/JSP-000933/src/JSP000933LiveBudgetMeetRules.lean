import JSP000933GroundBudgetDifferenceCalculus

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type} [Fintype I]

theorem finite_budget_unary_r233 (E R : BudgetExpr I) (A : I → bSet B) (n : ℕ)
    (h : ∀ a, E.groundHolds a n → R.groundHolds a n) :
    E.namedValue A n ≤ R.namedValue A n := by
  let P (_ : Fin 1) := E
  have hh := finite_budget_rule_r231 P R A n (fun a hA => h a (hA 0))
  exact (le_iInf (fun _ : Fin 1 => le_rfl)).trans hh

theorem finite_budget_binary_r233 (E F R : BudgetExpr I) (A : I → bSet B) (n : ℕ)
    (h : ∀ a, E.groundHolds a n → F.groundHolds a n → R.groundHolds a n) :
    E.namedValue A n ⊓ F.namedValue A n ≤ R.namedValue A n := by
  let P (i : Fin 2) := if i=0 then E else F
  have hh : ∀ a, (∀ i, (P i).groundHolds a n) → R.groundHolds a n := by
    intro a hA
    exact h a (by simpa [P] using hA 0) (by simpa [P] using hA 1)
  apply (show E.namedValue A n ⊓ F.namedValue A n ≤ ⨅ i, (P i).namedValue A n from ?_).trans
    (finite_budget_rule_r231 P R A n hh)
  apply le_iInf
  intro i
  by_cases he : i=0
  · simpa [P,he] using (inf_le_left : E.namedValue A n ⊓ F.namedValue A n ≤ E.namedValue A n)
  · simpa [P,he] using (inf_le_right : E.namedValue A n ⊓ F.namedValue A n ≤ F.namedValue A n)

def bitsMeet (x y : ℕ → B) : ℕ → B := fun n => x n ⊓ y n

def bitsJoin (x y : ℕ → B) : ℕ → B := fun n => x n ⊔ y n

def bitsComplement (x : ℕ → B) : ℕ → B := fun n => (x n)ᶜ

def tripleBitProfiles (x y z : ℕ → B) (i : Fin 3) : ℕ → B :=
  if i=0 then x else if i=1 then y else z

private theorem groundMeet_rightCover_r233 (A C D : Set ℕ) :
    A \ (C ∩ D) ⊆ (A \ C) ∪ (A \ D) := by
  classical
  intro i hi
  by_cases hC : i∈C
  · exact Or.inr ⟨hi.1,fun hD => hi.2 ⟨hC,hD⟩⟩
  · exact Or.inl ⟨hi.1,hC⟩

theorem nameBudgetValue_meet_right_r233 (h : Bool) (x y z : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName x) (realBitsName y) (2*k) n ⊓
      nameBudgetValue h (realBitsName x) (realBitsName z) (2*k) n ≤
    nameBudgetValue h (realBitsName x) (realBitsName (bitsMeet y z)) k n := by
  let E : BudgetExpr (Fin 3) := ⟨h,.var 0,.var 1,2*k⟩
  let F : BudgetExpr (Fin 3) := ⟨h,.var 0,.var 2,2*k⟩
  let R : BudgetExpr (Fin 3) := ⟨h,.var 0,.meet (.var 1) (.var 2),k⟩
  let A (i : Fin 3) := realBitsName (tripleBitProfiles x y z i)
  have hG (a : Fin 3 → Set ℕ) : E.groundHolds a n → F.groundHolds a n → R.groundHolds a n :=
    fun hE hF => GroundBudgetHolds.of_diff_cover_r232 h k n (groundMeet_rightCover_r233 (a 0) (a 1) (a 2)) hE hF
  have hL := finite_budget_binary_r233 E F R A n hG
  simp [E,F,R,A,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.evalB,
    tripleBitProfiles,membershipBits_realBitsName_r128] at hL
  exact hL

theorem nameBudgetValue_meet_right_elim_r233 (h : Bool) (x y z : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName x) (realBitsName (bitsMeet y z)) k n ≤
      nameBudgetValue h (realBitsName x) (realBitsName y) k n ⊓
        nameBudgetValue h (realBitsName x) (realBitsName z) k n := by
  let E : BudgetExpr (Fin 3) := ⟨h,.var 0,.meet (.var 1) (.var 2),k⟩
  let R : BudgetExpr (Fin 3) := ⟨h,.var 0,.var 1,k⟩
  let S : BudgetExpr (Fin 3) := ⟨h,.var 0,.var 2,k⟩
  let A (i : Fin 3) := realBitsName (tripleBitProfiles x y z i)
  have hR (a : Fin 3 → Set ℕ) : E.groundHolds a n → R.groundHolds a n := by
    intro hh
    exact GroundBudgetHolds.of_diff_subset_r232 h k n
      (show a 0 \ a 1 ⊆ a 0 \ (a 1 ∩ a 2) from fun _ hi => ⟨hi.1,fun hc => hi.2 hc.1⟩) hh
  have hS (a : Fin 3 → Set ℕ) : E.groundHolds a n → S.groundHolds a n := by
    intro hh
    exact GroundBudgetHolds.of_diff_subset_r232 h k n
      (show a 0 \ a 2 ⊆ a 0 \ (a 1 ∩ a 2) from fun _ hi => ⟨hi.1,fun hc => hi.2 hc.2⟩) hh
  have hL := le_inf (finite_budget_unary_r233 E R A n hR) (finite_budget_unary_r233 E S A n hS)
  simp [E,R,S,A,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.evalB,
    tripleBitProfiles,membershipBits_realBitsName_r128] at hL
  exact le_inf hL.1 hL.2

end SetLanguage
end JSP000933
