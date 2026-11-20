import JSP000933CantorMaskCongruence
import JSP000933MaskedCliqueName

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def membershipBits (x : bSet B) : ℕ → B :=
  fun n => bSet.of_nat n ∈ᴮ x

theorem membershipBits_realBitsName_r128 (x : ℕ → B) : membershipBits (realBitsName x) = x := by
  funext n
  change ((bSet.of_nat n : bSet B) ∈ᴮ familyName
    (fun k : ULift ℕ => bSet.of_nat k.down) (fun k => x k.down)) = x n
  refine mem_familyName_self_r70 (fun k : ULift ℕ => (bSet.of_nat k.down : bSet B)) ?_
    (fun k => x k.down) ⟨n⟩
  intro i j h
  apply bSet.check_bv_eq_bot_of_not_equiv
  apply PSet.ofNat_inj
  intro hh
  exact h (by cases i; cases j; cases hh; rfl)

theorem le_realEq_of_nameEq_r128 {p : B} {x y : bSet B} (h : p ≤ x =ᴮ y) :
    p ≤ realEqValue (membershipBits x) (membershipBits y) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  apply le_antisymm
  · exact le_inf inf_le_left (bSet.subst_congr_mem_right' (inf_le_left.trans h) inf_le_right)
  · exact le_inf inf_le_left (bSet.subst_congr_mem_right'
      (inf_le_left.trans (h.trans_eq bSet.bv_eq_symm)) inf_le_right)

theorem realBitsName_eq_r128 (x y : ℕ → B) :
    (realBitsName x =ᴮ realBitsName y) = realEqValue x y := by
  apply le_antisymm
  · simpa only [membershipBits_realBitsName_r128] using
      (le_realEq_of_nameEq_r128 (x := realBitsName x) (y := realBitsName y) le_rfl)
  · let p := realEqValue x y
    have h := (le_realEqValue_iff_r126 p x y).mp le_rfl
    refine (le_inf ?_ ?_).trans (bSet.eq_of_subset_subset (realBitsName x) (realBitsName y))
    · rw [bSet.subset_unfold]
      change p ≤ ⨅ n : ULift ℕ, imp (x n.down) ((bSet.of_nat n.down : bSet B) ∈ᴮ realBitsName y)
      apply le_iInf
      intro i
      rw [← _root_.deduction]
      have hi := congrFun (membershipBits_realBitsName_r128 y) i.down
      exact ((h i.down).le.trans inf_le_right).trans_eq hi.symm
    · rw [bSet.subset_unfold]
      change p ≤ ⨅ n : ULift ℕ, imp (y n.down) ((bSet.of_nat n.down : bSet B) ∈ᴮ realBitsName x)
      apply le_iInf
      intro i
      rw [← _root_.deduction]
      have hi := congrFun (membershipBits_realBitsName_r128 x) i.down
      exact ((h i.down).ge.trans inf_le_right).trans_eq hi.symm

theorem le_nameEq_of_realEq_for_subsets_r128 {p : B} {x y : bSet B}
    (hx : p ≤ x ⊆ᴮ bSet.omega) (hy : p ≤ y ⊆ᴮ bSet.omega)
    (he : p ≤ realEqValue (membershipBits x) (membershipBits y)) :
    p ≤ x =ᴮ y := by
  have h₁ := realBitsName_represents_r103 x hx
  have h₂ := realBitsName_represents_r103 y hy
  have hp : p ≤ realBitsName (membershipBits x) =ᴮ realBitsName (membershipBits y) :=
    he.trans_eq (realBitsName_eq_r128 _ _).symm
  exact bSet.bv_trans h₁ (bSet.bv_trans hp (h₂.trans_eq bSet.bv_eq_symm))

theorem actualDomain_extensional_r128 {I : Type} (x : I → ℕ → B) (S : bSet B)
    (i j : I) :
    (realBitsName (x j) ∈ᴮ S) ⊓ realEqValue (x i) (x j) ≤ realBitsName (x i) ∈ᴮ S := by
  rw [← realBitsName_eq_r128]
  exact bSet.subst_congr_mem_left' (inf_le_right.trans_eq bSet.bv_eq_symm) inf_le_left

theorem bSetColor_ext_left_r128 (K : Word × Word → B) (y : bSet B) :
    bSet.B_ext (fun x : bSet B => colorValue K (membershipBits x) (membershipBits y)) := by
  intro x z
  exact (mask_colorValue_congr_r127 K (le_realEq_of_nameEq_r128 le_rfl)
    ((le_realEqValue_iff_r126 _ _ _).mpr (fun _ => rfl))).le.trans inf_le_right

theorem bSetColor_ext_right_r128 (K : Word × Word → B) (x : bSet B) :
    bSet.B_ext (fun y : bSet B => colorValue K (membershipBits x) (membershipBits y)) := by
  intro y z
  exact (mask_colorValue_congr_r127 K ((le_realEqValue_iff_r126 _ _ _).mpr (fun _ => rfl))
    (le_realEq_of_nameEq_r128 le_rfl)).le.trans inf_le_right

end BooleanNames
end JSP000933
