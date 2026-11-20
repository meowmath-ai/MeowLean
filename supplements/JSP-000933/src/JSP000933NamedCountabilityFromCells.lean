import JSP000933ModelOCACoverTransfer
import JSP000933BooleanFunctionalGraphs

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem weakUnique_of_isFunc_r245 (C f : bSet B) {p : B} (h : p ≤ bSet.is_func f) :
    p ≤ weakUniqueValue C f := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [← _root_.deduction]
  exact bSet.eq_of_is_func_of_eq (inf_le_left.trans h) bSet.bv_refl
    (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))
    (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))

theorem namedCountable_of_cells_r245 (C : bSet B) (p : B)
    (cells : ℕ → (ℕ → B) → B) (hExt : ∀ n, RealTestExt (cells n))
    (hR : p ≤ namedAllRealsValue C)
    (hCov : ∀ x : ℕ → B, p ⊓ (realBitsName x ∈ᴮ C) ≤ ⨆ n, cells n x)
    (hU : ∀ n (x y : ℕ → B),
      p ⊓ ((realBitsName x ∈ᴮ C) ⊓ ((realBitsName y ∈ᴮ C) ⊓ (cells n x ⊓ cells n y))) ≤ realEqValue x y) :
    p ≤ weakCountabilityValue C := by
  classical
  let d (x : ℕ → B) := realBitsName x ∈ᴮ C
  let E (n : ℕ) := p ⊓ (⨆ x : ℕ → B, d x ⊓ cells n x)
  have hD : RealTestExt d := nativeDomain_ext_r179 C
  have hSelect (n : ℕ) : ∃ y : ℕ → B, E n ≤ d y ⊓ cells n y :=
    exists_realName_maximum_r138 (fun x => d x ⊓ cells n x) (hD.inf_r138 (hExt n)) (E n) inf_le_right
  choose y hy using hSelect
  let numbers (n : ℕ) : bSet B := bSet.of_nat n
  let names (n : ℕ) := realBitsName (y n)
  let f := functionalGraphName numbers names
  have hFunc : (⊤ : B) ≤ bSet.is_func f :=
    functionValue_functionalGraph_r102 numbers names (fun _ _ h => checkedNat_eq_bot_r174 h)
  apply le_iSup_of_le f
  refine le_inf (weakUnique_of_isFunc_r245 C f (le_top.trans hFunc)) ?_
  apply le_iInf
  intro A
  rw [← _root_.deduction]
  let q := p ⊓ (A ∈ᴮ C)
  let x := membershipBits A
  obtain ⟨hSub,hX⟩ := in_named_subset_bitName_r179 (inf_le_left.trans hR)
    (show q ≤ A ∈ᴮ C from inf_le_right)
  have he : q ≤ A =ᴮ realBitsName x := realBitsName_represents_r103 A hSub
  have hh : q ≤ ⨆ n, cells n x := (le_inf inf_le_left hX).trans (hCov x)
  apply (le_inf le_rfl hh).trans
  apply Lattice.bv_cases_right
  intro n
  let r := q ⊓ cells n x
  have hP : r ≤ p := inf_le_left.trans inf_le_left
  have hDx : r ≤ d x := inf_le_left.trans hX
  have hE : r ≤ E n := le_inf hP (le_iSup_of_le x (le_inf hDx inf_le_right))
  have hY : r ≤ d (y n) ⊓ cells n (y n) := hE.trans (hy n)
  have hRbit : r ≤ realEqValue x (y n) :=
    (le_inf hP (le_inf hDx (le_inf (hY.trans inf_le_left) (le_inf inf_le_right (hY.trans inf_le_right))))).trans
      (hU n x (y n))
  have hName : r ≤ A =ᴮ names n :=
    bSet.bv_trans (inf_le_left.trans he) (hRbit.trans_eq (realBitsName_eq_r128 x (y n)).symm)
  have hPair : r ≤ bSet.pair (numbers n) (names n) =ᴮ bSet.pair (numbers n) A :=
    bSet.pair_congr bSet.bv_refl (hName.trans_eq bSet.bv_eq_symm)
  apply le_iSup_of_le (numbers n)
  exact le_inf bSet.omega_definite (bSet.subst_congr_mem_left' hPair
    (le_top.trans (pair_mem_functionalGraph_self_r102 numbers names n)))

end SetLanguage
end JSP000933
