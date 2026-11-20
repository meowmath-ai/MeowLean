import JSP000933BooleanTwoStep
import JSP000933BooleanEnumerations

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanTwoStep OpenGraphForcing

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

def bSetStage (carrier order : bSet B)
    (hrefl : ∀ q : bSet B, (q ∈ᴮ carrier) ≤ bSet.pair q q ∈ᴮ order)
    (htrans : ∀ q r s : bSet B, (bSet.pair q r ∈ᴮ order) ⊓ (bSet.pair r s ∈ᴮ order)
      ≤ bSet.pair q s ∈ᴮ order) : Stage B (bSet B) :=
  ⟨fun q => q ∈ᴮ carrier,fun q r => bSet.pair q r ∈ᴮ order,hrefl,htrans⟩

variable {carrier ord : bSet B}
variable {hrefl : ∀ q : bSet B, (q ∈ᴮ carrier) ≤ bSet.pair q q ∈ᴮ ord}
variable {htrans : ∀ q r s : bSet B, (bSet.pair q r ∈ᴮ ord) ⊓ (bSet.pair r s ∈ᴮ ord)
  ≤ bSet.pair q s ∈ᴮ ord}

local notation "S" => bSetStage carrier ord hrefl htrans

theorem compVal_of_admitted_eq_r79 {p : B} {x y : bSet B}
    (ha : p ≤ (S).admitted x) (he : p ≤ x =ᴮ y) :
    p ≤ (S).compVal x y := by
  apply le_iSup_of_le x
  have hxx := ha.trans ((S).reflVal x)
  have hxy : p ≤ bSet.pair x y ∈ᴮ ord :=
    bSet.subst_congr_mem_left' (bSet.pair_congr bSet.bv_refl he) hxx
  exact le_inf ha (le_inf hxx hxy)

theorem compVal_congr_r79 {p : B} {x x' y y' : bSet B}
    (hx : p ≤ x =ᴮ x') (hy : p ≤ y =ᴮ y') (hc : p ≤ (S).compVal x y) :
    p ≤ (S).compVal x' y' := by
  apply (le_inf le_rfl hc).trans
  unfold Stage.compVal
  apply Lattice.bv_cases_right
  intro t
  apply le_iSup_of_le t
  apply le_inf (inf_le_right.trans inf_le_left)
  apply le_inf
  · exact bSet.subst_congr_mem_left'
      (bSet.pair_congr bSet.bv_refl (inf_le_left.trans hx))
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
  · exact bSet.subst_congr_mem_left'
      (bSet.pair_congr bSet.bv_refl (inf_le_left.trans hy))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))

def indexedFamilyName (f : OmegaOneIndex → bSet B) (g : OmegaOneIndex → B) : bSet B :=
  familyName (fun i : ULift.{u} OmegaOneIndex => f i.down) (fun i => g i.down)

theorem mem_indexedFamilyName_r79 (f : OmegaOneIndex → bSet B) (g : OmegaOneIndex → B) (z : bSet B) :
    (z ∈ᴮ indexedFamilyName f g) = ⨆ i, g i ⊓ (z =ᴮ f i) := by
  rw [indexedFamilyName,mem_familyName_r70]
  exact le_antisymm
    (iSup_le (fun i => le_iSup (fun j => g j ⊓ (z =ᴮ f j)) i.down))
    (iSup_le (fun i => le_iSup (fun j : ULift.{u} OmegaOneIndex => g j.down ⊓ (z =ᴮ f j.down)) ⟨i⟩))

theorem indexedFamilyName_subset_r79 (f : OmegaOneIndex → bSet B) (g : OmegaOneIndex → B)
    (ha : ∀ i, g i ≤ (S).admitted (f i)) :
    (indexedFamilyName f g ⊆ᴮ carrier) = ⊤ := by
  apply top_unique
  rw [bSet.subset_unfold]
  change (⊤ : B) ≤ ⨅ i : ULift.{u} OmegaOneIndex, imp (g i.down) ((S).admitted (f i.down))
  apply le_iInf
  intro i
  rw [← _root_.deduction,top_inf_eq]
  exact ha i.down

noncomputable def antichainValue (D : Stage B (bSet B)) (w : bSet B) : B :=
  ⨅ x : bSet B, ⨅ y : bSet B,
    imp ((x ∈ᴮ w) ⊓ (y ∈ᴮ w)) ((x =ᴮ y) ⊔ (D.compVal x y)ᶜ)

theorem indexedFamilyName_antichain_r79 (f : OmegaOneIndex → bSet B) (g : OmegaOneIndex → B)
    (hanti : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) ((S).compVal (f i) (f j))) :
    antichainValue S (indexedFamilyName f g) = ⊤ := by
  classical
  apply top_unique
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← _root_.deduction,top_inf_eq,mem_indexedFamilyName_r79]
  apply Lattice.bv_cases_left
  intro i
  rw [mem_indexedFamilyName_r79]
  apply Lattice.bv_cases_right
  intro j
  let c := (g i ⊓ (x =ᴮ f i)) ⊓ (g j ⊓ (y =ᴮ f j))
  have hx : c ≤ x =ᴮ f i := inf_le_left.trans inf_le_right
  have hy : c ≤ y =ᴮ f j := inf_le_right.trans inf_le_right
  by_cases h : i = j
  · subst j
    exact (bSet.bv_trans hx (hy.trans_eq bSet.bv_eq_symm)).trans le_sup_left
  · refine le_trans ?_ le_sup_right
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hfg : c ≤ g i ⊓ g j := le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)
    have hCompat : c ⊓ (S).compVal x y ≤ (S).compVal (f i) (f j) :=
      compVal_congr_r79 (inf_le_left.trans hx) (inf_le_left.trans hy) inf_le_right
    exact (le_inf (inf_le_left.trans hfg) hCompat).trans (disjoint_iff_inf_le.mp (hanti i j h))

end BooleanNames
end JSP000933
