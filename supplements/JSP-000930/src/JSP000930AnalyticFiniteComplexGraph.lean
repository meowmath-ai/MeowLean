import JSP000930AnalyticComplexBasic
import JSP000933BooleanFunctionalGraphs

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option backward.isDefEq.respectTransparency false

theorem bTruth_and_eq {n : ℕ} (v : DVec (V B) n) (f g : SForm n) :
    bTruth v (bd_and f g) = bTruth v f ⊓ bTruth v g :=
  boolean_realize_bounded_formula_and

def finiteComplexGraph (N : ℕ) (f : ℕ → ComplexBits B) : bSet B :=
  functionalGraphName (fun i : Fin N => bSet.of_nat i.val) (fun i => (f i.val).name)

theorem bTruth_value {n : ℕ} (v : DVec (V B) n) (g k z : STerm n) :
    bTruth v (value_f g k z) = (bSet.pair (bTerm v k) (bTerm v z) ∈ᴮ bTerm v g) := by
  simp only [value_f,boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair']

theorem finiteComplexGraph_value (N : ℕ) (f : ℕ → ComplexBits B) (i : Fin N) (z : bSet B) :
    (bSet.pair (bSet.of_nat i.val) z ∈ᴮ finiteComplexGraph N f) = (z =ᴮ (f i.val).name) := by
  rw [finiteComplexGraph,pair_mem_functionalGraph_r102]
  simp only [checkedNat_eq_crisp_r189]
  apply le_antisymm
  · refine iSup_le fun j : Fin N => ?_
    by_cases h : i.val = j.val
    · have he : i = j := Fin.ext h
      subst j
      exact inf_le_right
    · simp [crispTruth,h]
  · refine le_iSup_of_le i ?_
    simp [crispTruth]

theorem forces_complexBits_name {n : ℕ} (v : DVec (V B) n) (Z : STerm n)
    (z : ComplexBits B) (p : B) (hZ : bTerm v Z = z.name) (hz : z.CutOn p) :
    p ≤ bTruth v (complex_f Z) := by
  apply forces_complex_pair_of_cutData v Z z.re z.im p _ hz.1 hz.2
  rw [hZ]
  exact le_top.trans bSet.bv_refl

private theorem familyName_top_forall {I : Type} (x : I → bSet B) (F : bSet B → B)
    (hF : bSet.B_ext F) :
    (⨅ z : bSet B, imp (z ∈ᴮ familyName x (fun _ => ⊤)) (F z)) = ⨅ i, F (x i) := by
  have hmem (z : bSet B) : (z ∈ᴮ familyName x (fun _ => ⊤)) = ⨆ i, z =ᴮ x i := by
    simp only [mem_familyName_r70,top_inf_eq]
  apply le_antisymm
  · refine le_iInf fun i => ?_
    have h := iInf_le (fun z : bSet B => imp (z ∈ᴮ familyName x (fun _ => ⊤)) (F z)) (x i)
    have hm : (x i ∈ᴮ familyName x (fun _ => ⊤)) = (⊤ : B) := by
      rw [hmem]
      exact top_unique (bSet.bv_refl.trans (le_iSup (fun j => x i =ᴮ x j) i))
    rw [hm] at h
    have h' : imp (⊤ : B) (F (x i)) ≤ imp ⊤ (F (x i)) := le_rfl
    rw [← _root_.deduction,inf_top_eq] at h'
    exact h.trans h'
  · let p : B := ⨅ i, F (x i)
    change p ≤ _
    refine le_iInf fun z => ?_
    rw [← _root_.deduction,hmem,inf_iSup_eq]
    refine iSup_le fun i => ?_
    calc
      p ⊓ (z =ᴮ x i) ≤ F (x i) ⊓ (z =ᴮ x i) :=
        inf_le_inf_right _ (iInf_le _ i)
      _ = (x i =ᴮ z) ⊓ F (x i) := by rw [inf_comm,bSet.bv_eq_symm]
      _ ≤ F z := hF (x i) z

theorem finiteComplexGraph_forall {n : ℕ} (v : DVec (V B) n) (G : STerm n)
    (N : ℕ) (f : ℕ → ComplexBits B) (hG : bTerm v G = finiteComplexGraph N f)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn G φ) = ⨅ i : Fin N,
      bTruth (DVec.cons (bSet.pair (bSet.of_nat i.val) (f i.val).name) v)
        (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  rw [bTruth_allIn_r181,hG,finiteComplexGraph,functionalGraphName]
  exact familyName_top_forall _ _ (bTruth_body_ext_r191 v _)

set_option maxHeartbeats 600000 in
theorem forces_typedFiniteComplexGraph {n : ℕ} (v : DVec (V B) n)
    (G A : STerm n) (N : ℕ) (f : ℕ → ComplexBits B) (p : B)
    (hG : bTerm v G = finiteComplexGraph N f) (hA : bTerm v A = bSet.of_nat N)
    (hf : ∀ i : Fin N, (f i.val).CutOn p) :
    p ≤ bTruth v (typedComplexFunctionOn_f G A) := by
  change p ≤ bTruth v (bd_and
    (allIn G (fun q => exIn (up A) (fun i => sEx (fun z =>
      bd_and (complex_f z) (bd_equal (up2 q) (pair' (up i) z))))))
    (allIn A (fun i => sEx (fun z => bd_and (complex_f z)
      (bd_and (value_f (up2 G) (up i) z) (sAll (fun w =>
        bd_imp (value_f (up3 G) (up2 i) w) (bd_equal (up z) w))))))))
  rw [bTruth_and_eq]
  apply le_inf
  · rw [finiteComplexGraph_forall v G N f hG]
    refine le_iInf fun i => ?_
    let x := bSet.pair (bSet.of_nat i.val) (f i.val).name
    let vx : DVec (V B) (n+1) := DVec.cons x v
    let S : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    have hAx : bTerm vx (up A) = bSet.of_nat N := (bTerm_up_r181 v x A).trans hA
    rw [bTruth_exIn_r181,hAx]
    apply le_iSup_of_le (bSet.of_nat i.val)
    refine le_inf ?_ ?_
    · rw [checkedNat_mem_r174,ite_eq_left i.isLt]
      exact le_top
    rw [bTruth_sEx_r181]
    apply le_iSup_of_le (f i.val).name
    let vi : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) i.val) vx
    let vz : DVec (V B) (n+3) := DVec.cons (f i.val).name vi
    let J : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
    let Z : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    change p ≤ bTruth vz (bd_and (complex_f Z) (bd_equal (up2 S) (pair' (up J) Z)))
    rw [bTruth_and_eq]
    apply le_inf (forces_complexBits_name vz Z (f i.val) p (bTerm_current_r181 vi _) (hf i))
    simp only [bTruth_equal_r181,boolean_realize_bounded_term_pair',vz,vi,vx,S,J,Z,
      bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,x]
    exact le_top.trans bSet.bv_refl
  · rw [bTruth_boundedForallNat_r191 v A N hA]
    refine le_iInf fun i => ?_
    rw [bTruth_sEx_r181]
    apply le_iSup_of_le (f i.val).name
    let vi : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) i.val) v
    let vz : DVec (V B) (n+2) := DVec.cons (f i.val).name vi
    let I : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    let Z : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
    change p ≤ bTruth vz (bd_and (complex_f Z)
      (bd_and (value_f (up2 G) (up I) Z) (sAll (fun w =>
        bd_imp (value_f (up3 G) (up2 I) w) (bd_equal (up Z) w)))))
    simp only [bTruth_and_eq]
    refine le_inf (forces_complexBits_name vz Z (f i.val) p (bTerm_current_r181 vi _) (hf i))
      (le_inf ?_ ?_)
    · simp only [bTruth_value,vz,vi,I,Z,bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,hG,
        finiteComplexGraph_value N f i]
      exact le_top.trans bSet.bv_refl
    · simp only [bTruth_sAll_r181,bTruth_imp_r181,bTruth_value,bTruth_equal_r181,
        vz,vi,I,Z,bTerm_up_r181,bTerm_up2_r181,bTerm_up3_r181,bTerm_current_r181,hG,
        finiteComplexGraph_value N f i]
      refine le_iInf fun w => ?_
      rw [← _root_.deduction]
      exact inf_le_right.trans_eq bSet.bv_eq_symm

end JSP000930.AnalyticSyntax
