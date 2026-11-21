import JSP000930PositiveWeightedComplexImpliesProperCuts
import JSP000930PositiveEntireTaylorNameCover

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option backward.isDefEq.respectTransparency false

theorem sequence_total_retains_complex {n : ℕ} (v : DVec (V B) n) (A : STerm n)
    (p : B) (hA : p ≤ bTruth v (sequence_f A)) (k : ℕ) :
    p ≤ ⨆ z : bSet B,
      bTruth (DVec.cons z (DVec.cons (bSet.of_nat k) v))
          (complex_f (bd_var ⟨0,Nat.succ_pos (n+1)⟩)) ⊓
        (pair (bSet.of_nat k) z ∈ᴮ bTerm v A) := by
  unfold sequence_f typedComplexFunctionOn_f at hA
  simp only [boolean_realize_bounded_formula_and] at hA
  have h := hA.trans inf_le_right
  simp only [bTruth_allIn_r181,bTruth_sEx_r181,bTruth_sAll_r181,
    bTruth_equal_r181,bTruth_imp_r181,boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    value_f,bTerm_liftOne,bTerm_liftTwo,bTerm_liftThree,bTerm_current_r181,
    boolean_realize_bounded_term_omega'] at h
  have hk : (⊤ : B) ≤ (bSet.of_nat k : bSet B) ∈ᴮ bSet.omega :=
    bSet.of_nat_mem_omega
  have he := (le_inf (h.trans (iInf_le _ (bSet.of_nat k))) (le_top.trans hk)).trans
    Lattice.bv_imp_elim
  refine he.trans (iSup_le (fun z => le_iSup_of_le z ?_))
  exact le_inf inf_le_left (inf_le_right.trans inf_le_left)

theorem sequence_graphTaylorBits_proper {n : ℕ} (v : DVec (V B) n) (A : STerm n)
    (p : B) (hA : p ≤ bTruth v (sequence_f A)) (k : ℕ) (b : Bool) :
    ProperCutOn p (fun q => graphTaylorBits (bTerm v A) (k,b,q)) := by
  let G := bTerm v A
  let N : bSet B := bSet.of_nat k
  let U := graphTaylorBits G
  have h := hA.trans (typedComplexFunction_le_native v A
    (JSP000933.SetLanguage.omega : STerm n))
  rw [show bTerm v (JSP000933.SetLanguage.omega : STerm n) = bSet.omega from
    boolean_realize_bounded_term_omega'] at h
  have hF := typedGraph_func (h.trans inf_le_left) (h.trans inf_le_right)
  have hMember := graphTaylorBits_named_coeff_mem G p hF
    (typedGraph_good_total_omega (h.trans inf_le_right)) k
  let w (z : bSet B) := DVec.cons z (DVec.cons N v)
  let Z : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let cell (z : bSet B) : B := p ⊓
    (bTruth (w z) (complex_f Z) ⊓ (pair N z ∈ᴮ G))
  have hCover : p ≤ ⨆ z : bSet B,cell z := by
    change p ≤ ⨆ z : bSet B,p ⊓ (bTruth (w z) (complex_f Z) ⊓ (pair N z ∈ᴮ G))
    rw [← inf_iSup_eq]
    exact le_inf le_rfl (sequence_total_retains_complex v A p hA k)
  apply properCutOn_mono hCover
  apply properCutOn_iSup
  intro z
  have hEq : cell z ≤ bTerm (w z) Z =ᴮ coefficientName U k := by
    rw [show bTerm (w z) Z = z from bTerm_current_r181 (DVec.cons N v) z]
    exact eq_of_is_func_of_eq (inf_le_left.trans hF) bv_refl
      (inf_le_right.trans inf_le_right) (inf_le_left.trans hMember)
  have hBoth := properCutOn_of_weighted_complex (w z) Z
    (fun q => U (k,false,q)) (fun q => U (k,true,q)) (cell z) hEq
    (inf_le_right.trans inf_le_left)
  cases b
  · exact hBoth.1
  · exact hBoth.2

end JSP000930.Positive
