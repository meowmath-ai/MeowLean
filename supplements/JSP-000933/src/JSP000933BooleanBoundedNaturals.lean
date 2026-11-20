import JSP000933FiniteRecursionCrisp

open Fol Lattice
open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open BooleanNames PositiveForcing CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_vecMask_r191 {n : ℕ} (p : B) (v w : DVec (V B) n) (φ : SForm n)
    (h : ∀ i : Fin n, p ≤ (v.nth i.val i.isLt =ᴮ w.nth i.val i.isLt)) :
    p ⊓ bTruth v φ = p ⊓ bTruth w φ := by
  have hBoth {a b : DVec (V B) n}
      (he : ∀ i : Fin n, p ≤ (a.nth i.val i.isLt =ᴮ b.nth i.val i.isLt)) :
      p ⊓ bTruth a φ ≤ bTruth b φ := by
    have hvec : p ≤ ⨅ i : Fin n, (V B).eq (a.nth i.val i.isLt) (b.nth i.val i.isLt) :=
      le_iInf he
    exact (inf_le_inf_right _ hvec).trans
      (boolean_realize_bounded_formula_congr (S := V B)
        ⟨(∅ : bSet B)⟩ a b φ DVec.nil)
  exact le_antisymm (le_inf inf_le_left (hBoth h))
    (le_inf inf_le_left (hBoth (fun i => (h i).trans_eq bSet.bv_eq_symm)))

theorem bTruth_body_ext_r191 {n : ℕ} (v : DVec (V B) n) (φ : SForm (n+1)) :
    bSet.B_ext (fun x : bSet B => bTruth (DVec.cons x v) φ) := by
  intro x y
  let p : B := x =ᴮ y
  have hEq : p ⊓ bTruth (DVec.cons x v) φ = p ⊓ bTruth (DVec.cons y v) φ := by
    apply bTruth_vecMask_r191
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact bSet.bv_refl
  exact hEq.le.trans inf_le_right

theorem omega_exists_r191 (F : bSet B → B) (hF : bSet.B_ext F) :
    (⨆ x : bSet B, (x ∈ᴮ bSet.omega) ⊓ F x) = ⨆ i : ℕ, F (bSet.of_nat i) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [memberOmega_cases_r174]
    apply Lattice.bv_cases_left
    intro i
    exact (hF x (bSet.of_nat i)).trans (le_iSup (fun j : ℕ => F (bSet.of_nat j)) i)
  · apply iSup_le
    intro i
    apply le_iSup_of_le (bSet.of_nat i)
    exact le_inf bSet.omega_definite le_rfl

theorem checkedNat_exists_r191 (n : ℕ) (F : bSet B → B) (hF : bSet.B_ext F) :
    (⨆ x : bSet B, (x ∈ᴮ bSet.of_nat n) ⊓ F x) = ⨆ i : Fin n, F (bSet.of_nat i.val) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [memberCheckedNat_cases_r174]
    apply Lattice.bv_cases_left
    intro i
    exact (hF x (bSet.of_nat i.val)).trans (le_iSup (fun j : Fin n => F (bSet.of_nat j.val)) i)
  · apply iSup_le
    intro i
    apply le_iSup_of_le (bSet.of_nat i.val)
    refine le_inf ?_ le_rfl
    rw [checkedNat_mem_r174,ite_eq_left i.isLt]
    exact le_top

theorem bTruth_boundedForallOmega_r191 {n : ℕ} (v : DVec (V B) n)
    (t : STerm n) (ht : bTerm v t = bSet.omega) (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn t φ) = ⨅ i : ℕ,
      bTruth (DVec.cons (bSet.of_nat i) v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  rw [bTruth_allIn_r181,ht]
  exact omega_forall_r174 _ (bTruth_body_ext_r191 v _)

theorem bTruth_boundedExistsOmega_r191 {n : ℕ} (v : DVec (V B) n)
    (t : STerm n) (ht : bTerm v t = bSet.omega) (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (exIn t φ) = ⨆ i : ℕ,
      bTruth (DVec.cons (bSet.of_nat i) v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  rw [bTruth_exIn_r181,ht]
  exact omega_exists_r191 _ (bTruth_body_ext_r191 v _)

theorem bTruth_boundedForallNat_r191 {n : ℕ} (v : DVec (V B) n)
    (t : STerm n) (k : ℕ) (ht : bTerm v t = bSet.of_nat k)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn t φ) = ⨅ i : Fin k,
      bTruth (DVec.cons (bSet.of_nat i.val) v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  rw [bTruth_allIn_r181,ht]
  exact checkedNat_forall_r174 k _ (bTruth_body_ext_r191 v _)

end SetLanguage
end JSP000933
