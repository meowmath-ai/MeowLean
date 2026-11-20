import JSP000933BooleanInternalCCC

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanTwoStep

universe u
variable {B T : Type u} [NontrivialCompleteBooleanAlgebra B] [Preorder T]

abbrev EdgeIndex (T : Type u) [Preorder T] := {q : T × T // q.1 ≤ q.2}

theorem pair_mem_groundOrder_r81 (label : T → bSet B) (x y : bSet B) :
    (bSet.pair x y ∈ᴮ groundEdgeName label (· ≤ ·)) =
      ⨆ q : EdgeIndex T, (x =ᴮ label q.1.1) ⊓ (y =ᴮ label q.1.2) := by
  rw [groundEdgeName,mem_familyName_r70]
  simp only [top_inf_eq]
  apply congrArg (fun f : EdgeIndex T → B => iSup f)
  funext q
  apply le_antisymm
  · exact le_inf bSet.eq_of_eq_pair_left bSet.eq_of_eq_pair_right
  · exact bSet.pair_congr inf_le_left inf_le_right

theorem pair_mem_groundOrder_self_r81 [DecidableRel ((· ≤ ·) : T → T → Prop)]
    (label : T → bSet B) (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (x y : T) :
    (bSet.pair (label x) (label y) ∈ᴮ groundEdgeName label (· ≤ ·)) =
      if x ≤ y then ⊤ else ⊥ := by
  by_cases hxy : x ≤ y
  · rw [ite_eq_left hxy]
    exact top_unique (pair_mem_groundEdge_r72 label _ hxy)
  · rw [ite_eq_right hxy,pair_mem_groundOrder_r81]
    apply le_bot_iff.mp
    apply iSup_le
    intro q
    by_cases hx : x = q.1.1
    · have hy : y ≠ q.1.2 := by
        intro he
        apply hxy
        rw [hx,he]
        exact q.2
      exact inf_le_right.trans_eq (hLabel _ _ hy)
    · exact inf_le_left.trans_eq (hLabel _ _ hx)

theorem groundOrder_refl_r81 (label : T → bSet B) (V : T → B) (x : bSet B) :
    (x ∈ᴮ familyName label V) ≤ bSet.pair x x ∈ᴮ groundEdgeName label (· ≤ ·) := by
  rw [mem_familyName_r70,pair_mem_groundOrder_r81]
  apply iSup_le
  intro i
  exact le_iSup_of_le (⟨(i,i),le_rfl⟩ : EdgeIndex T) (le_inf inf_le_right inf_le_right)

theorem groundOrder_trans_r81 (label : T → bSet B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (x y z : bSet B) :
    (bSet.pair x y ∈ᴮ groundEdgeName label (· ≤ ·)) ⊓
      (bSet.pair y z ∈ᴮ groundEdgeName label (· ≤ ·)) ≤
      bSet.pair x z ∈ᴮ groundEdgeName label (· ≤ ·) := by
  rw [pair_mem_groundOrder_r81,pair_mem_groundOrder_r81,pair_mem_groundOrder_r81]
  apply Lattice.bv_cases_left
  intro a
  apply Lattice.bv_cases_right
  intro b
  let c := ((x =ᴮ label a.1.1) ⊓ (y =ᴮ label a.1.2)) ⊓
    ((y =ᴮ label b.1.1) ⊓ (z =ᴮ label b.1.2))
  by_cases he : a.1.2 = b.1.1
  · have hAB : a.1.1 ≤ b.1.2 := a.2.trans (he.symm ▸ b.2)
    exact le_iSup_of_le (⟨(a.1.1,b.1.2),hAB⟩ : EdgeIndex T)
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
  · have hya : c ≤ y =ᴮ label a.1.2 := inf_le_left.trans inf_le_right
    have hyb : c ≤ y =ᴮ label b.1.1 := inf_le_right.trans inf_le_left
    have hEq : c ≤ label a.1.2 =ᴮ label b.1.1 :=
      bSet.bv_trans (hya.trans_eq bSet.bv_eq_symm) hyb
    exact (hEq.trans_eq (hLabel _ _ he)).trans bot_le

def groundLabelStage (label : T → bSet B) (V : T → B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) : Stage B (bSet B) :=
  bSetStage (familyName label V) (groundEdgeName label (· ≤ ·))
    (groundOrder_refl_r81 label V) (groundOrder_trans_r81 label hLabel)

end BooleanNames
end JSP000933
