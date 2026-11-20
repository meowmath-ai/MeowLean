import JSP000933ActualNativeOCATop

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing FiniteSupport

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem maskedCoverage_le_r171 (p : B) (g : I → B) :
    p ⊓ countableCoverageValue (fun i => p ⊓ g i) ≤ countableCoverageValue g := by
  unfold countableCoverageValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro e
  apply le_iSup_of_le e
  apply le_iInf
  intro i
  let covered := ⨆ n, e.1 n i
  let value := matrixCoverage (fun i => p ⊓ g i) e
  have hTest : value ≤ (p ⊓ g i)ᶜ ⊔ covered :=
    iInf_le (fun j => (p ⊓ g j)ᶜ ⊔ (⨆ n, e.1 n j)) i
  have hImp := (le_materialImp_iff_r126 value (p ⊓ g i) covered).mp hTest
  apply (le_materialImp_iff_r126 (p ⊓ value) (g i) covered).mpr
  calc
    (p ⊓ value) ⊓ g i = value ⊓ (p ⊓ g i) := by ac_rfl
    _ ≤ covered := hImp

theorem masked_nonCountable_r171 (p : B) (g : I → B) (h : p ≤ (countableCoverageValue g)ᶜ) :
    p ≤ (countableCoverageValue (fun i => p ⊓ g i))ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  have hh : p ⊓ countableCoverageValue (fun i => p ⊓ g i) ≤ p ⊓ countableCoverageValue g :=
    le_inf inf_le_left (maskedCoverage_le_r171 p g)
  exact hh.trans (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp h))

theorem weightedClique_masked_r171 (D : (ℕ → B) → B) (K : Word × Word → B)
    (x : OmegaOneIndex → ℕ → B) (g : OmegaOneIndex → B) (p : B)
    (h : p ≤ weightedCliqueValue D K x g) :
    (∀ i, p ⊓ g i ≤ D (x i)) ∧
    (∀ i j, i ≠ j → (p ⊓ g i) ⊓ (p ⊓ g j) ≤
      colorValue K (x i) (x j) ⊓ (realEqValue (x i) (x j))ᶜ) ∧
    p ≤ (countableCoverageValue (fun i => p ⊓ g i))ᶜ := by
  refine ⟨?_,?_,masked_nonCountable_r171 p g (h.trans (inf_le_right.trans inf_le_right))⟩
  · intro i
    exact (le_materialImp_iff_r126 p (g i) (D (x i))).mp
      (h.trans (inf_le_left.trans (iInf_le _ i)))
  · intro i j hne
    let a : {a : OmegaOneIndex × OmegaOneIndex // a.1 ≠ a.2} := ⟨(i,j),hne⟩
    have h0 := h.trans (inf_le_right.trans (inf_le_left.trans (iInf_le _ a)))
    have h1 := (le_materialImp_iff_r126 p (g i ⊓ g j)
      (colorValue K (x i) (x j) ⊓ (realEqValue (x i) (x j))ᶜ)).mp h0
    exact (le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).trans h1

end CantorCodes
end JSP000933
