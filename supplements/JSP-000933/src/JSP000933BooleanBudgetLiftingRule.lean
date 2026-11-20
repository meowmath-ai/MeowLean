import JSP000933NamedBooleanSetExpressions

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type}

structure BudgetExpr (I : Type) where
  harmonic : Bool
  left : SetBitExpr I
  right : SetBitExpr I
  scale : ℕ

def BudgetExpr.groundHolds (E : BudgetExpr I) (a : I → Set ℕ) (n : ℕ) : Prop :=
  GroundBudgetHolds E.harmonic (E.left.groundSet a) (E.right.groundSet a) E.scale n

noncomputable def BudgetExpr.namedValue (E : BudgetExpr I) (A : I → bSet B) (n : ℕ) : B :=
  nameBudgetValue E.harmonic (E.left.namedSet A) (E.right.namedSet A) E.scale n

theorem BudgetExpr.maskGround_r231 (E : BudgetExpr I) (A : I → bSet B) (a : I → Set ℕ)
    (n : ℕ) (q : B)
    (h : ∀ i j, j<n →
      q ⊓ membershipBits (A i) j = q ⊓ membershipBits (groundSubsetName B (a i)) j) :
    q ⊓ E.namedValue A n = q ⊓ crispTruth B (E.groundHolds a n) :=
  nameBudgetValue_locallyCrisp_r226 (E.left.named_maskGround_r230 A a n q h)
    (E.right.named_maskGround_r230 A a n q h) E.harmonic E.scale

theorem finite_budget_rule_r231 [Fintype I] {m : ℕ} (E : Fin m → BudgetExpr I) (R : BudgetExpr I)
    (A : I → bSet B) (n : ℕ)
    (h : ∀ a : I → Set ℕ, (∀ i, (E i).groundHolds a n) → R.groundHolds a n) :
    (⨅ i, (E i).namedValue A n) ≤ R.namedValue A n := by
  apply le_of_dense_named_refinements_r219
  intro p hp hP
  obtain ⟨a,q,hq,hqp,hMask⟩ := exists_joint_finiteGroundProfiles_r227 A n p hp
  have hEach (i : Fin m) : (E i).groundHolds a n :=
    prop_of_le_crisp_nonzero_r190 hq
      (((le_inf le_rfl (hqp.trans (hP.trans (iInf_le _ i)))).trans_eq
        ((E i).maskGround_r231 A a n q hMask)).trans inf_le_right)
  have hR := h a hEach
  have hTop : crispTruth B (R.groundHolds a n) = (⊤ : B) := by
    simp [crispTruth,hR]
  exact ⟨q,hq,hqp,((le_inf le_rfl (le_top.trans_eq hTop.symm)).trans_eq
    (R.maskGround_r231 A a n q hMask).symm).trans inf_le_right⟩

theorem SetBitExpr.named_var_canonical_r231 (x : I → ℕ → B) (i : I) :
    (SetBitExpr.var i).namedSet (fun j => realBitsName (x j)) = realBitsName (x i) := by
  unfold SetBitExpr.namedSet SetBitExpr.evalB
  simp only [membershipBits_realBitsName_r128]

end SetLanguage
end JSP000933
