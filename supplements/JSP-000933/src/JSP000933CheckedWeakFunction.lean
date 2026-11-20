import JSP000933CheckedArithmetic

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem iSup_crispEquality_select_r193 (n : ℕ) (F : ℕ → B) :
    (⨆ m, crispTruth B (m = n) ⊓ F m) = F n := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro m
    by_cases h : m = n
    · subst m
      exact inf_le_right
    · simp [crispTruth,h]
  · have h := le_iSup (fun m => crispTruth B (m = n) ⊓ F m) n
    simpa [crispTruth] using h

theorem iInf_crispEquality_select_r193 (n : ℕ) (F : ℕ → B) :
    (⨅ m, imp (crispTruth B (m = n)) (F m)) = F n := by
  classical
  apply le_antisymm
  · have h := iInf_le (fun m => imp (crispTruth B (m = n)) (F m)) n
    simpa [crispTruth,_root_.imp] using h
  · apply le_iInf
    intro m
    by_cases h : m = n
    · subst m
      simp [crispTruth,_root_.imp]
    · simp [crispTruth,_root_.imp,h]

theorem exists_unique_boolean_r193 (v : ℕ → B) :
    (⨆ y, v y ⊓ ⨅ z, imp (v z) (crispTruth B (y = z))) =
      (⨆ y, v y) ⊓ (⨅ y, ⨅ z, imp (v y ⊓ v z) (crispTruth B (y = z))) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    refine le_inf (inf_le_left.trans (le_iSup v a)) ?_
    apply le_iInf
    intro y
    apply le_iInf
    intro z
    rw [← _root_.deduction]
    let q := (v a ⊓ ⨅ w, imp (v w) (crispTruth B (a = w))) ⊓ (v y ⊓ v z)
    have hUni (w : ℕ) : q ≤ imp (v w) (crispTruth B (a = w)) :=
      inf_le_left.trans (inf_le_right.trans (iInf_le _ w))
    have hY := _root_.context_imp_elim (hUni y) (show q ≤ v y from inf_le_right.trans inf_le_left)
    have hZ := _root_.context_imp_elim (hUni z) (show q ≤ v z from inf_le_right.trans inf_le_right)
    have hh := (le_inf hY hZ).trans_eq (crisp_and_r190 (B := B) (a=y) (a=z)).symm
    by_cases he : y = z
    · simp [crispTruth,he]
    · have hN : ¬ (a = y ∧ a = z) := fun h => he (h.1.symm.trans h.2)
      exact (hh.trans_eq (by simp [crispTruth,hN])).trans bot_le
  · rw [iSup_inf_eq]
    apply iSup_le
    intro y
    apply le_iSup_of_le y
    refine le_inf inf_le_left ?_
    apply le_iInf
    intro z
    rw [← _root_.deduction]
    let q := (v y ⊓ (⨅ y, ⨅ z, imp (v y ⊓ v z) (crispTruth B (y = z)))) ⊓ v z
    have hU : q ≤ imp (v y ⊓ v z) (crispTruth B (y = z)) :=
      inf_le_left.trans (inf_le_right.trans ((iInf_le _ y).trans (iInf_le _ z)))
    exact _root_.context_imp_elim hU (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

theorem iInf_inf_separate_r193 {I : Type*} (f g : I → B) :
    (⨅ i, f i ⊓ g i) = (⨅ i, f i) ⊓ (⨅ i, g i) := by
  apply le_antisymm
  · exact le_inf (le_iInf (fun i => (iInf_le _ i).trans inf_le_left))
      (le_iInf (fun i => (iInf_le _ i).trans inf_le_right))
  · exact le_iInf (fun i => le_inf (inf_le_left.trans (iInf_le _ i))
      (inf_le_right.trans (iInf_le _ i)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bTruth_naturalFunction_checked_r193 {n : ℕ}
    (v : DVec (V B) n) (g domain : STerm n) (m : ℕ)
    (hd : bTerm v domain = bSet.of_nat (m+1)) :
    bTruth v (naturalFunctionOn_f g domain) =
      natTableTotal (bTerm v g) m ⊓ natTableUnique (bTerm v g) m := by
  unfold naturalFunctionOn_f
  rw [bTruth_boundedForallNat_r191 v domain (m+1) hd]
  simp only [bTruth_exOmega_r192,bTruth_allOmega_r192,boolean_realize_bounded_formula_and,
    bTruth_imp_r181,bTruth_equal_r181,value_f,boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair',bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,
    bTerm_up3_r181,checkedNat_eq_crisp_r189]
  change (⨅ i : Fin (m+1), ⨆ y : ℕ, valueAtNat (bTerm v g) i.val y ⊓
    (⨅ z : ℕ, imp (valueAtNat (bTerm v g) i.val z) (crispTruth B (y = z)))) = _
  simp only [exists_unique_boolean_r193,iInf_inf_separate_r193,natTableTotal,natTableUnique]

end SetLanguage
end JSP000933
