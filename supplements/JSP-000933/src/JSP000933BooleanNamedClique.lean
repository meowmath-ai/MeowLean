import JSP000933BooleanNames
import JSP000933BooleanCliqueStage

open scoped Flypitch bSet
open Lattice

namespace JSP000933
namespace BooleanNames

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type u}

def realCheckName (x : ℕ → Bool) : bSet B :=
  familyName (fun k : ULift.{u} ℕ => bSet.of_nat k.down)
    (fun k => if x k.down = true then ⊤ else ⊥)

theorem realCheckName_coordinate_r72 (x : ℕ → Bool) (n : ℕ) :
    ((bSet.of_nat n : bSet B) ∈ᴮ realCheckName x) = (if x n = true then ⊤ else ⊥) := by
  change ((bSet.of_nat n : bSet B) ∈ᴮ familyName (fun k : ULift.{u} ℕ =>
    bSet.of_nat k.down) (fun k => if x k.down = true then ⊤ else ⊥)) = _
  refine mem_familyName_self_r70 (fun k : ULift.{u} ℕ => (bSet.of_nat k.down : bSet B)) ?_
    (fun k => if x k.down = true then ⊤ else ⊥) ⟨n⟩
  intro i j hij
  have hn : i.down ≠ j.down := by
    intro h
    apply hij
    cases i
    cases j
    cases h
    rfl
  exact bSet.check_bv_eq_bot_of_not_equiv (PSet.ofNat_inj hn)

theorem realCheckName_subset_omega_r72 (x : ℕ → Bool) :
    (realCheckName x : bSet B) ⊆ᴮ bSet.omega = ⊤ := by
  apply top_unique
  rw [bSet.subset_unfold]
  apply le_iInf
  intro i
  rw [← _root_.deduction]
  exact bSet.omega_definite

theorem realCheckName_eq_bot_of_ne_r72 {x y : ℕ → Bool} (h : x ≠ y) :
    ((realCheckName x : bSet B) =ᴮ realCheckName y) = ⊥ := by
  classical
  have hn : ∃ n, x n ≠ y n := by
    by_contra hc
    apply h
    funext n
    by_contra he
    exact hc ⟨n,he⟩
  obtain ⟨n,hn⟩ := hn
  apply le_bot_iff.mp
  have hxy := bSet.subst_congr_mem_right
    (u := (bSet.of_nat n : bSet B)) (v := realCheckName x) (w := realCheckName y)
  have hyx := bSet.subst_congr_mem_right
    (u := (bSet.of_nat n : bSet B)) (v := realCheckName y) (w := realCheckName x)
  rw [show ((realCheckName y : bSet B) =ᴮ realCheckName x) =
    (realCheckName x =ᴮ realCheckName y) from bSet.bv_eq_symm] at hyx
  rw [realCheckName_coordinate_r72,realCheckName_coordinate_r72] at hxy hyx
  cases hx : x n <;> cases hy : y n
  · exact False.elim (hn (hx.trans hy.symm))
  · simpa [hx,hy] using hyx
  · simpa [hx,hy] using hxy
  · exact False.elim (hn (hx.trans hy.symm))

def groundEdgeName (a : I → bSet B) (edge : I → I → Prop) : bSet B :=
  familyName (fun q : {q : I × I // edge q.1 q.2} => bSet.pair (a q.1.1) (a q.1.2))
    (fun _ => ⊤)

theorem pair_mem_groundEdge_r72 (a : I → bSet B) (edge : I → I → Prop) {i j : I}
    (h : edge i j) : (⊤ : B) ≤ bSet.pair (a i) (a j) ∈ᴮ groundEdgeName a edge := by
  rw [groundEdgeName,mem_familyName_r70]
  exact le_iSup_of_le (⟨(i,j),h⟩ : {q : I × I // edge q.1 q.2})
    (by rw [bSet.bv_eq_refl,top_inf_eq])

noncomputable def nameIsClique (s edgeName : bSet B) : B :=
  ⨅ x : bSet B, ⨅ y : bSet B,
    imp ((x ∈ᴮ s) ⊓ (y ∈ᴮ s)) ((x =ᴮ y) ⊔ (bSet.pair x y ∈ᴮ edgeName))

theorem familyName_isClique_r72 (a : I → bSet B) (g : I → B)
    (edge : I → I → Prop)
    (hForbid : ∀ i j, i ≠ j → ¬ edge i j → Disjoint (g i) (g j)) :
    nameIsClique (familyName a g) (groundEdgeName a edge) = ⊤ := by
  classical
  apply top_unique
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← _root_.deduction,top_inf_eq,mem_familyName_r70]
  apply Lattice.bv_cases_left
  intro i
  rw [mem_familyName_r70]
  apply Lattice.bv_cases_right
  intro j
  let c := (g i ⊓ (x =ᴮ a i)) ⊓ (g j ⊓ (y =ᴮ a j))
  have hx : c ≤ x =ᴮ a i := inf_le_left.trans inf_le_right
  have hy : c ≤ y =ᴮ a j := inf_le_right.trans inf_le_right
  by_cases h : i = j
  · subst j
    exact (bSet.bv_trans hx (hy.trans_eq bSet.bv_eq_symm)).trans le_sup_left
  · by_cases he : edge i j
    · have hp : c ≤ bSet.pair (a i) (a j) =ᴮ bSet.pair x y :=
        (bSet.pair_congr hx hy).trans_eq bSet.bv_eq_symm
      exact (bSet.subst_congr_mem_left' hp (le_top.trans (pair_mem_groundEdge_r72 a edge he))).trans
        le_sup_right
    · have hh : c ≤ g i ⊓ g j := le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)
      exact hh.trans ((disjoint_iff_inf_le.mp (hForbid i j h he)).trans bot_le)

end BooleanNames
end JSP000933
