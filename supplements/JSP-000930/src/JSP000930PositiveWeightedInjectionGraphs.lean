import JSP000933BooleanFunctionalGraphs
import Flypitch4.BvmExtras

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames

universe u
variable {B I : Type u} [NontrivialCompleteBooleanAlgebra B]

def weightedGraph (x y : I → bSet B) (w : I → B) : bSet B :=
  familyName (fun i => pair (x i) (y i)) w

theorem pair_mem_weightedGraph (x y : I → bSet B) (w : I → B) (a c : bSet B) :
    (pair a c ∈ᴮ weightedGraph x y w) =
      ⨆ i, w i ⊓ ((a =ᴮ x i) ⊓ (c =ᴮ y i)) := by
  rw [weightedGraph,mem_familyName_r70]
  apply congrArg (fun f : I → B => iSup f)
  funext i
  have h : (pair a c =ᴮ pair (x i) (y i)) = ((a =ᴮ x i) ⊓ (c =ᴮ y i)) :=
    le_antisymm (le_inf eq_of_eq_pair_left eq_of_eq_pair_right)
      (pair_congr inf_le_left inf_le_right)
  rw [h]

theorem weightedGraph_func (x y : I → bSet B) (w : I → B)
    (h : ∀ i j, (w i ⊓ w j) ⊓ (x i =ᴮ x j) ≤ (y i =ᴮ y j)) :
    (⊤ : B) ≤ is_func (weightedGraph x y w) := by
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro d
  rw [← deduction,top_inf_eq,← deduction,
    pair_mem_weightedGraph,pair_mem_weightedGraph,iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  rintro ⟨i,j⟩
  let l := w i ⊓ ((a =ᴮ x i) ⊓ (c =ᴮ y i))
  let r := w j ⊓ ((b =ᴮ x j) ⊓ (d =ᴮ y j))
  let v := (l ⊓ r) ⊓ (a =ᴮ b)
  have hL : v ≤ l := inf_le_left.trans inf_le_left
  have hR : v ≤ r := inf_le_left.trans inf_le_right
  have ha : v ≤ a =ᴮ x i := hL.trans (inf_le_right.trans inf_le_left)
  have hb : v ≤ b =ᴮ x j := hR.trans (inf_le_right.trans inf_le_left)
  have hc : v ≤ c =ᴮ y i := hL.trans (inf_le_right.trans inf_le_right)
  have hd : v ≤ d =ᴮ y j := hR.trans (inf_le_right.trans inf_le_right)
  have he : v ≤ x i =ᴮ x j := bv_trans (bv_symm ha) (bv_trans inf_le_right hb)
  have hf : v ≤ y i =ᴮ y j :=
    (le_inf (le_inf (hL.trans inf_le_left) (hR.trans inf_le_left)) he).trans (h i j)
  exact bv_trans hc (bv_trans hf (bv_symm hd))

theorem weightedGraph_inj (x y : I → bSet B) (w : I → B)
    (h : ∀ i j, (w i ⊓ w j) ⊓ (y i =ᴮ y j) ≤ (x i =ᴮ x j)) :
    (⊤ : B) ≤ is_inj (weightedGraph x y w) := by
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro d
  rw [← deduction,top_inf_eq,
    pair_mem_weightedGraph,pair_mem_weightedGraph,iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  rintro ⟨i,j⟩
  let l := w i ⊓ ((a =ᴮ x i) ⊓ (c =ᴮ y i))
  let r := w j ⊓ ((b =ᴮ x j) ⊓ (d =ᴮ y j))
  let v := (l ⊓ r) ⊓ (c =ᴮ d)
  have hL : v ≤ l := inf_le_left.trans inf_le_left
  have hR : v ≤ r := inf_le_left.trans inf_le_right
  have ha : v ≤ a =ᴮ x i := hL.trans (inf_le_right.trans inf_le_left)
  have hb : v ≤ b =ᴮ x j := hR.trans (inf_le_right.trans inf_le_left)
  have hc : v ≤ c =ᴮ y i := hL.trans (inf_le_right.trans inf_le_right)
  have hd : v ≤ d =ᴮ y j := hR.trans (inf_le_right.trans inf_le_right)
  have he : v ≤ y i =ᴮ y j := bv_trans (bv_symm hc) (bv_trans inf_le_right hd)
  have hf : v ≤ x i =ᴮ x j :=
    (le_inf (le_inf (hL.trans inf_le_left) (hR.trans inf_le_left)) he).trans (h i j)
  exact bv_trans ha (bv_trans hf (bv_symm hb))

theorem weightedGraph_total (x y : I → bSet B) (w : I → B)
    (D R : bSet B)
    (hCover : ∀ a,(a ∈ᴮ D) ≤ ⨆ i,w i ⊓ (a =ᴮ x i))
    (hRange : ∀ i,(⊤ : B) ≤ y i ∈ᴮ R) :
    (⊤ : B) ≤ is_total D R (weightedGraph x y w) := by
  apply le_iInf
  intro a
  rw [← deduction,top_inf_eq]
  apply (hCover a).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le (y i)
  refine le_inf (le_top.trans (hRange i)) ?_
  rw [pair_mem_weightedGraph]
  apply le_iSup_of_le i
  exact le_inf inf_le_left (le_inf inf_le_right bv_refl)

theorem weightedGraph_injects_into (x y : I → bSet B) (w : I → B)
    (D R : bSet B)
    (hF : ∀ i j, (w i ⊓ w j) ⊓ (x i =ᴮ x j) ≤ (y i =ᴮ y j))
    (hI : ∀ i j, (w i ⊓ w j) ⊓ (y i =ᴮ y j) ≤ (x i =ᴮ x j))
    (hCover : ∀ a,(a ∈ᴮ D) ≤ ⨆ i,w i ⊓ (a =ᴮ x i))
    (hRange : ∀ i,(⊤ : B) ≤ y i ∈ᴮ R) :
    (⊤ : B) ≤ injects_into D R :=
  le_iSup_of_le (weightedGraph x y w)
    (le_inf (le_inf (weightedGraph_func x y w hF)
      (weightedGraph_total x y w D R hCover hRange)) (weightedGraph_inj x y w hI))

end JSP000930.Positive
