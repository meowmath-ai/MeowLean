import Flypitch4.BvmExtras

open scoped Flypitch bSet
open Lattice

namespace JSP000933
namespace BooleanNames

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type u}

def familyName (a : I → bSet B) (g : I → B) : bSet B :=
  bSet.mk I a g

theorem mem_familyName_r70 (a : I → bSet B) (g : I → B) (z : bSet B) :
    (z ∈ᴮ familyName a g) = ⨆ i, g i ⊓ (z =ᴮ a i) := rfl

theorem mem_familyName_self_r70 (a : I → bSet B)
    (ha : ∀ i j, i ≠ j → (a i =ᴮ a j) = ⊥) (g : I → B) (i : I) :
    (a i ∈ᴮ familyName a g) = g i := by
  rw [mem_familyName_r70]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases h : i = j
    · subst j
      exact inf_le_left
    · rw [ha i j h,inf_bot_eq]
      exact bot_le
  · exact le_iSup_of_le i (by rw [bSet.bv_eq_refl,inf_top_eq])

theorem familyName_subset_ambient_r70 (a : I → bSet B) (g : I → B) :
    (familyName a g ⊆ᴮ familyName a (fun _ => ⊤)) = ⊤ := by
  apply top_unique
  rw [bSet.subset_unfold']
  apply le_iInf
  intro z
  rw [← _root_.deduction,top_inf_eq,mem_familyName_r70,mem_familyName_r70]
  exact iSup_le (fun i => le_iSup_of_le i (inf_le_inf_right _ le_top))

theorem familyName_represents_subset_r70 (a : I → bSet B) (w : bSet B) (p : B)
    (hp : p ≤ w ⊆ᴮ familyName a (fun _ => ⊤)) :
    p ≤ w =ᴮ familyName a (fun i => a i ∈ᴮ w) := by
  apply bSet.mem_ext
  · apply le_iInf
    intro z
    rw [← _root_.deduction]
    let c := p ⊓ (z ∈ᴮ w)
    have hDom : c ≤ z ∈ᴮ familyName a (fun _ => ⊤) :=
      bSet.mem_of_mem_subset (inf_le_left.trans hp) inf_le_right
    have ht : (z ∈ᴮ familyName a (fun _ => ⊤)) = ⨆ i, z =ᴮ a i := by
      rw [mem_familyName_r70]
      simp only [top_inf_eq]
    have hAbove : c ≤ c ⊓ (⨆ i, z =ᴮ a i) := le_inf le_rfl (hDom.trans_eq ht)
    apply hAbove.trans
    apply Lattice.bv_cases_right
    intro i
    rw [mem_familyName_r70]
    apply le_iSup_of_le i
    exact le_inf
      ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans bSet.subst_congr_mem_left)
      inf_le_right
  · apply le_iInf
    intro z
    rw [← _root_.deduction,mem_familyName_r70]
    apply Lattice.bv_cases_right
    intro i
    have hEq : p ⊓ ((a i ∈ᴮ w) ⊓ (z =ᴮ a i)) ≤ a i =ᴮ z :=
      (inf_le_right.trans inf_le_right).trans_eq bSet.bv_eq_symm
    exact (le_inf hEq (inf_le_right.trans inf_le_left)).trans bSet.subst_congr_mem_left

end BooleanNames
end JSP000933
