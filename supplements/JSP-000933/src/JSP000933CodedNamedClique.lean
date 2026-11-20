import JSP000933RealNameExtensionality

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open OpenGraphForcing

open CantorCodes

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedOpenClique (K : Word × Word → B) (C : bSet B) : B :=
  ⨅ x : bSet B, ⨅ y : bSet B,
    imp ((x ∈ᴮ C) ⊓ (y ∈ᴮ C))
      ((x =ᴮ y) ⊔ colorValue K (membershipBits x) (membershipBits y))

theorem familyName_namedOpenClique_r129 (K : Word × Word → B) (x : I → ℕ → B) (g : I → B)
    (h : ∀ i j, i ≠ j → g i ⊓ g j ≤ colorValue K (x i) (x j)) :
    namedOpenClique K (familyName (fun i => realBitsName (x i)) g) = ⊤ := by
  classical
  apply top_unique
  apply le_iInf
  intro u
  apply le_iInf
  intro v
  rw [← _root_.deduction,top_inf_eq,mem_familyName_r70]
  apply Lattice.bv_cases_left
  intro i
  rw [mem_familyName_r70]
  apply Lattice.bv_cases_right
  intro j
  let c := (g i ⊓ (u =ᴮ realBitsName (x i))) ⊓ (g j ⊓ (v =ᴮ realBitsName (x j)))
  have hu : c ≤ u =ᴮ realBitsName (x i) := inf_le_left.trans inf_le_right
  have hv : c ≤ v =ᴮ realBitsName (x j) := inf_le_right.trans inf_le_right
  by_cases he : i = j
  · subst j
    exact (bSet.bv_trans hu (hv.trans_eq bSet.bv_eq_symm)).trans le_sup_left
  · have hi : c ≤ realEqValue (membershipBits u) (x i) := by
        simpa only [membershipBits_realBitsName_r128] using le_realEq_of_nameEq_r128 hu
    have hj : c ≤ realEqValue (membershipBits v) (x j) := by
        simpa only [membershipBits_realBitsName_r128] using le_realEq_of_nameEq_r128 hv
    have hcert : c ≤ colorValue K (x i) (x j) :=
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)).trans (h i j he)
    have hMask := mask_colorValue_congr_r127 K hi hj
    exact ((le_inf le_rfl hcert).trans (hMask.ge.trans inf_le_right)).trans le_sup_right

theorem familyName_subset_of_memberships_r129 (a : I → bSet B) (g : I → B) (Y : bSet B)
    (h : ∀ i, g i ≤ a i ∈ᴮ Y) :
    (⊤ : B) ≤ familyName a g ⊆ᴮ Y := by
  rw [bSet.subset_unfold]
  change (⊤ : B) ≤ ⨅ i : I, imp (g i) (a i ∈ᴮ Y)
  apply le_iInf
  intro i
  rw [← _root_.deduction,top_inf_eq]
  exact h i

theorem exists_namedOpenClique_below_r129 (K : Word × Word → B) (D : bSet B)
    (x : I → ℕ → B) (g : I → B) (mark p : B)
    (activated : ∀ i, g i ≤ mark)
    (sep : ∀ i j, i ≠ j → Disjoint mark (realEqValue (x i) (x j)))
    (hD : ∀ i, g i ≤ realBitsName (x i) ∈ᴮ D)
    (hEdge : ∀ i j, i ≠ j → g i ⊓ g j ≤ colorValue K (x i) (x j))
    (hp : p ≤ (countableCoverageValue g)ᶜ) :
    ∃ C : bSet B, (⊤ : B) ≤ C ⊆ᴮ D ∧
      namedOpenClique K C = ⊤ ∧ p ≤ (hasOmegaEnumeration C)ᶜ := by
  refine ⟨familyName (fun i => realBitsName (x i)) g,
    familyName_subset_of_memberships_r129 _ _ _ hD,
    familyName_namedOpenClique_r129 K x g hEdge,?_⟩
  apply locDistinctName_forced_uncountable_r125 _ _ mark activated _ hp
  intro i j hne
  rw [realBitsName_eq_r128]
  exact sep i j hne

end BooleanNames
end JSP000933
