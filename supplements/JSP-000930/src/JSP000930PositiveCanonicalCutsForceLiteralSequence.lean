import JSP000930PositiveExactEvalCorrespondenceInterface
import JSP000930AnalyticFiniteComplexGraph

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000933.BooleanNames JSP000933.PositiveForcing
  JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option backward.isDefEq.respectTransparency false

theorem taylorCodeName_at (U : TaylorSlot → B) (i : ℕ) (z : bSet B) :
    (pair (bSet.of_nat i) z ∈ᴮ taylorCodeName U) = (z =ᴮ coefficientName U i) := by
  rw [taylorCodeName,pair_mem_functionalGraph_r102]
  simp only [checkedNat_eq_crisp_r189]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases h : i = j
    · subst j
      exact inf_le_right
    · simp [crispTruth,h]
  · apply le_iSup_of_le i
    simp [crispTruth]

theorem taylor_graph_all_pairs {n : ℕ} (v : DVec (V B) n) (T : STerm n)
    (U : TaylorSlot → B) (hT : bTerm v T = taylorCodeName U)
    (φ : STerm (n+1) → SForm (n+1)) (p : B)
    (h : ∀ i : ℕ,p ≤ bTruth (DVec.cons (pair (bSet.of_nat i) (coefficientName U i)) v)
      (φ (bd_var ⟨0,Nat.succ_pos n⟩))) :
    p ≤ bTruth v (allIn T φ) := by
  rw [bTruth_allIn_r181,hT]
  apply le_iInf
  intro y
  rw [← _root_.deduction]
  have hM : (y ∈ᴮ taylorCodeName U) =
      ⨆ i : ℕ,y =ᴮ pair (bSet.of_nat i) (coefficientName U i) := by
    simp only [taylorCodeName,functionalGraphName,mem_familyName_r70,top_inf_eq]
  rw [hM,inf_iSup_eq]
  apply iSup_le
  intro i
  let x := pair (bSet.of_nat i) (coefficientName U i)
  let f : SForm (n+1) := φ (bd_var ⟨0,Nat.succ_pos n⟩)
  exact (le_inf (bv_symm inf_le_right) (inf_le_left.trans (h i))).trans
    (bTruth_body_ext_r191 v f x y)

theorem forces_literal_sequence_of_canonical_cuts {n : ℕ}
    (v : DVec (V B) n) (G : STerm n) (U : TaylorSlot → B) (p : B)
    (hG : bTerm v G = taylorCodeName U)
    (hU : ∀ i,(complexCoeffBits U i).CutOn p) :
    p ≤ bTruth v (sequence_f G) := by
  change p ≤ bTruth v (bd_and
    (allIn G (fun q => exIn omega (fun i => sEx (fun z =>
      bd_and (complex_f z) (bd_equal (up2 q) (pair' (up i) z))))))
    (allIn omega (fun i => sEx (fun z => bd_and (complex_f z)
      (bd_and (value_f (up2 G) (up i) z) (sAll (fun w =>
        bd_imp (value_f (up3 G) (up2 i) w) (bd_equal (up z) w))))))))
  rw [bTruth_and_eq]
  apply le_inf
  · apply taylor_graph_all_pairs v G U hG
    intro i
    let x := pair (bSet.of_nat i) (coefficientName U i)
    let vx : DVec (V B) (n+1) := DVec.cons x v
    let S : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    have ho : bTerm vx JSP000933.SetLanguage.omega = bSet.omega := boolean_realize_bounded_term_omega'
    rw [bTruth_exIn_r181,ho]
    apply le_iSup_of_le (bSet.of_nat i)
    have hi : (⊤ : B) ≤ (bSet.of_nat i : bSet B) ∈ᴮ bSet.omega :=
      bSet.of_nat_mem_omega
    refine le_inf (le_top.trans hi) ?_
    rw [bTruth_sEx_r181]
    apply le_iSup_of_le (coefficientName U i)
    let vi : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) i) vx
    let vz : DVec (V B) (n+3) := DVec.cons (coefficientName U i) vi
    let J : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
    let Z : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    change p ≤ bTruth vz (bd_and (complex_f Z) (bd_equal (up2 S) (pair' (up J) Z)))
    rw [bTruth_and_eq]
    apply le_inf (weighted_complexName_forces_complex vz Z (complexCoeffBits U i)
      p (bTerm_current_r181 vi _) (hU i))
    simp only [bTruth_equal_r181,boolean_realize_bounded_term_pair',vz,vi,vx,S,J,Z,
      bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,x]
    exact bv_refl
  · rw [bTruth_allOmega_r192]
    refine le_iInf fun i => ?_
    rw [bTruth_sEx_r181]
    apply le_iSup_of_le (coefficientName U i)
    let vi : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) i) v
    let vz : DVec (V B) (n+2) := DVec.cons (coefficientName U i) vi
    let I : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    let Z : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
    change p ≤ bTruth vz (bd_and (complex_f Z)
      (bd_and (value_f (up2 G) (up I) Z) (sAll (fun w =>
        bd_imp (value_f (up3 G) (up2 I) w) (bd_equal (up Z) w)))))
    simp only [bTruth_and_eq]
    refine le_inf (weighted_complexName_forces_complex vz Z (complexCoeffBits U i) p
      (bTerm_current_r181 vi _) (hU i)) (le_inf ?_ ?_)
    · simp only [bTruth_value,vz,vi,I,Z,bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,hG,
        taylorCodeName_at U i]
      exact bv_refl
    · simp only [bTruth_sAll_r181,bTruth_imp_r181,bTruth_value,bTruth_equal_r181,
        vz,vi,I,Z,bTerm_up_r181,bTerm_up2_r181,bTerm_up3_r181,bTerm_current_r181,hG,
        taylorCodeName_at U i]
      refine le_iInf fun w => ?_
      rw [← _root_.deduction]
      exact inf_le_right.trans_eq bv_eq_symm

end JSP000930.Positive
