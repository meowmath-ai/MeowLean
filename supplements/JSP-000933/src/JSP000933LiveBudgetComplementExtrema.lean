import JSP000933LiveBudgetMeetRules

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def twoBitProfiles (x y : ℕ → B) (i : Fin 2) : ℕ → B :=
  if i=0 then x else y

theorem nameBudgetValue_compl_reverse_r234 (h : Bool) (x y : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName (bitsComplement y)) (realBitsName (bitsComplement x)) k n =
      nameBudgetValue h (realBitsName x) (realBitsName y) k n := by
  let E : BudgetExpr (Fin 2) := ⟨h,.neg (.var 1),.neg (.var 0),k⟩
  let R : BudgetExpr (Fin 2) := ⟨h,.var 0,.var 1,k⟩
  let A (i : Fin 2) := realBitsName (twoBitProfiles x y i)
  have hG (a : Fin 2 → Set ℕ) : E.groundHolds a n ↔ R.groundHolds a n :=
    GroundBudgetHolds.compl_iff_r232 h k n (a 0) (a 1)
  have hL := le_antisymm
    (finite_budget_unary_r233 E R A n (fun a => (hG a).mp))
    (finite_budget_unary_r233 R E A n (fun a => (hG a).mpr))
  simp [E,R,A,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.evalB,
    twoBitProfiles,membershipBits_realBitsName_r128] at hL
  exact hL

theorem GroundBudgetHolds.of_subset_r234 (h : Bool) (k n : ℕ) {A C : Set ℕ} (hs : A ⊆ C) :
    GroundBudgetHolds h A C k n := by
  apply GroundBudgetHolds.of_diff_subset_r232 h k n (D := A) (E := A) _ (GroundBudgetHolds.refl_r228 h A k n)
  intro i hi
  exact False.elim (hi.2 (hs hi.1))

theorem nameBudgetValue_of_groundExpr_subset_r234 {I : Type} [Fintype I]
    (A : I → bSet B) (h : Bool) (left right : SetBitExpr I) (k n : ℕ)
    (hs : ∀ a : I → Set ℕ, left.groundSet a ⊆ right.groundSet a) :
    (⊤ : B) ≤ nameBudgetValue h (left.namedSet A) (right.namedSet A) k n := by
  let E (i : Fin 0) : BudgetExpr I := Fin.elim0 i
  let R : BudgetExpr I := ⟨h,left,right,k⟩
  have hF := finite_budget_rule_r231 E R A n (fun a _ => GroundBudgetHolds.of_subset_r234 h k n (hs a))
  apply (show (⊤ : B) ≤ ⨅ i : Fin 0, (E i).namedValue A n from le_iInf (fun i => Fin.elim0 i)).trans
  exact hF

theorem nameBudgetValue_bot_r234 (h : Bool) (x : ℕ → B) (k n : ℕ) :
    (⊤ : B) ≤ nameBudgetValue h (realBitsName (fun _ => ⊥)) (realBitsName x) k n := by
  let A (_ : Unit) := realBitsName x
  have hS (a : Unit → Set ℕ) : (SetBitExpr.const false).groundSet a ⊆
      (SetBitExpr.var ()).groundSet a := by
    intro i hi
    have hf : false=true := hi
    cases hf
  have hF := nameBudgetValue_of_groundExpr_subset_r234 A h (.const false) (.var ()) k n hS
  simpa [A,SetBitExpr.namedSet,SetBitExpr.evalB,truthBit,membershipBits_realBitsName_r128] using hF

theorem nameBudgetValue_top_r234 (h : Bool) (x : ℕ → B) (k n : ℕ) :
    (⊤ : B) ≤ nameBudgetValue h (realBitsName x) (realBitsName (fun _ => ⊤)) k n := by
  let A (_ : Unit) := realBitsName x
  have hS (a : Unit → Set ℕ) : (SetBitExpr.var ()).groundSet a ⊆
      (SetBitExpr.const true).groundSet a := by
    intro i hi
    exact rfl
  have hF := nameBudgetValue_of_groundExpr_subset_r234 A h (.var ()) (.const true) k n hS
  simpa [A,SetBitExpr.namedSet,SetBitExpr.evalB,truthBit,membershipBits_realBitsName_r128] using hF

@[simp] theorem bitsComplement_compl_r234 (x : ℕ → B) : bitsComplement (bitsComplement x) = x := by
  funext i
  exact compl_compl _

theorem bitsJoin_deMorgan_r234 (x y : ℕ → B) :
    bitsJoin x y = bitsComplement (bitsMeet (bitsComplement x) (bitsComplement y)) := by
  funext i
  simp only [bitsJoin,bitsComplement,bitsMeet,compl_inf,compl_compl]

end SetLanguage
end JSP000933
