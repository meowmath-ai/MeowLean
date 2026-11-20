import JSP000933BooleanSmallLabels

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] {I : Type u}

def functionalGraphName (x y : I → bSet B) : bSet B :=
  familyName (fun i => bSet.pair (x i) (y i)) (fun _ => ⊤)

theorem pair_mem_functionalGraph_r102 (x y : I → bSet B) (a b : bSet B) :
    (bSet.pair a b ∈ᴮ functionalGraphName x y) =
      ⨆ i, (a =ᴮ x i) ⊓ (b =ᴮ y i) := by
  rw [functionalGraphName,mem_familyName_r70]
  simp only [top_inf_eq]
  apply congrArg (fun f : I → B => iSup f)
  funext i
  exact le_antisymm (le_inf bSet.eq_of_eq_pair_left bSet.eq_of_eq_pair_right)
    (bSet.pair_congr inf_le_left inf_le_right)

theorem pair_mem_functionalGraph_self_r102 (x y : I → bSet B) (i : I) :
    (⊤ : B) ≤ bSet.pair (x i) (y i) ∈ᴮ functionalGraphName x y :=
  bSet.mem_mk (fun j => bSet.pair (x j) (y j)) (fun _ => ⊤) i

theorem functionValue_functionalGraph_r102 (x y : I → bSet B)
    (sep : ∀ i j, i ≠ j → (x i =ᴮ x j) = ⊥) :
    (⊤ : B) ≤ bSet.is_func (functionalGraphName x y) := by
  classical
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro d
  rw [← _root_.deduction,top_inf_eq,← _root_.deduction,
    pair_mem_functionalGraph_r102,pair_mem_functionalGraph_r102,inf_assoc]
  apply Lattice.bv_cases_left
  intro i
  rw [iSup_inf_eq]
  apply Lattice.bv_cases_right
  intro j
  let v := ((a =ᴮ x i) ⊓ (c =ᴮ y i)) ⊓ (((b =ᴮ x j) ⊓ (d =ᴮ y j)) ⊓ (a =ᴮ b))
  have hc : v ≤ c =ᴮ y i := inf_le_left.trans inf_le_right
  have hd : v ≤ d =ᴮ y j := inf_le_right.trans (inf_le_left.trans inf_le_right)
  by_cases he : i = j
  · subst j
    exact bSet.bv_trans hc (hd.trans_eq bSet.bv_eq_symm)
  · have ha : v ≤ a =ᴮ x i := inf_le_left.trans inf_le_left
    have hb : v ≤ b =ᴮ x j := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hab : v ≤ a =ᴮ b := inf_le_right.trans inf_le_right
    have hh : v ≤ x i =ᴮ x j :=
      bSet.bv_trans (ha.trans_eq bSet.bv_eq_symm) (bSet.bv_trans hab hb)
    exact (hh.trans_eq (sep i j he)).trans bot_le

theorem totalValue_functionalGraph_r102 (x y : I → bSet B) (R : bSet B)
    (hRange : ∀ i, (⊤ : B) ≤ y i ∈ᴮ R) :
    (⊤ : B) ≤ bSet.is_total (familyName x (fun _ => ⊤)) R (functionalGraphName x y) := by
  apply le_iInf
  intro a
  rw [← _root_.deduction,top_inf_eq,mem_familyName_r70]
  apply iSup_le
  intro i
  apply le_iSup_of_le (y i)
  apply le_inf (le_top.trans (hRange i))
  have hPair : (⊤ ⊓ (a =ᴮ x i) : B) ≤ bSet.pair (x i) (y i) =ᴮ bSet.pair a (y i) :=
    bSet.pair_congr (inf_le_right.trans_eq bSet.bv_eq_symm) bSet.bv_refl
  exact bSet.subst_congr_mem_left' hPair (le_top.trans (pair_mem_functionalGraph_self_r102 x y i))

end BooleanNames
end JSP000933
