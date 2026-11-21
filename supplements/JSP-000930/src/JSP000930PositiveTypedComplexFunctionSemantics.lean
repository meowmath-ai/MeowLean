import JSP000930PositiveReconstructMixedTaylorGraph
import JSP000930AnalyticComplexPair
import JSP000930AnalyticRationalTruth

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option backward.isDefEq.respectTransparency false

noncomputable def weakComplexName (z : bSet B) : B :=
  ⨆ x : bSet B,⨆ y : bSet B, ((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)) ⊓ (z =ᴮ pair x y)

theorem realCut_le_subset_rationals {n : ℕ} (v : DVec (V B) n) (X : STerm n) :
    bTruth v (realCut_f X) ≤ bTerm v X ⊆ᴮ ratUniverse := by
  unfold realCut_f
  simp only [boolean_realize_bounded_formula_and]
  apply (inf_le_right.trans inf_le_left).trans
  change bTruth v (allIn X fun q => rationalCode_f q) ≤ _
  rw [bTruth_allIn_r181]
  simp only [bTruth_rationalCode,bTerm_current_r181]
  rw [bSet.subset_unfold]
  exact (bounded_forall (v := bTerm v X) (ϕ := fun x => x ∈ᴮ (ratUniverse : bSet B))
    (h_congr := B_ext_mem_left)).ge

theorem bTruth_complex_le_weak {n : ℕ} (v : DVec (V B) n) (Z : STerm n) :
    bTruth v (complex_f Z) ≤ weakComplexName (bTerm v Z) := by
  rw [bTruth_complex_expand]
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply le_iSup_of_le x
  apply le_iSup_of_le y
  apply inf_le_inf ?_ le_rfl
  apply inf_le_inf
  · exact realCut_le_subset_rationals (complexCoordinates v x y) realCoordinate_f
  · exact realCut_le_subset_rationals (complexCoordinates v x y) imagCoordinate_f

noncomputable def graphTypedShape (G A : bSet B) : B :=
  ⨅ q : bSet B,imp (q ∈ᴮ G) (⨆ i : bSet B,(i ∈ᴮ A) ⊓
    (⨆ z : bSet B,weakComplexName z ⊓ (q =ᴮ pair i z)))

noncomputable def graphTypedTotalUnique (G A : bSet B) : B :=
  ⨅ i : bSet B,imp (i ∈ᴮ A) (⨆ z : bSet B,weakComplexName z ⊓
    ((pair i z ∈ᴮ G) ⊓
      (⨅ w : bSet B,imp (pair i w ∈ᴮ G) (z =ᴮ w))))

theorem bTerm_liftOne {n : ℕ} (v : DVec (V B) n) (x : bSet B) (t : STerm n) :
    bTerm (DVec.cons x v) (lift_bounded_term t 1) = bTerm v t :=
  bTerm_up_r181 v x t

theorem bTerm_liftTwo {n : ℕ} (v : DVec (V B) n)
    (x y : bSet B) (t : STerm n) :
    bTerm (DVec.cons y (DVec.cons x v)) (lift_bounded_term t 2) = bTerm v t :=
  bTerm_up2_r181 v x y t

theorem bTerm_liftThree {n : ℕ} (v : DVec (V B) n)
    (x y z : bSet B) (t : STerm n) :
    bTerm (DVec.cons z (DVec.cons y (DVec.cons x v))) (lift_bounded_term t 3) = bTerm v t :=
  bTerm_up3_r181 v x y z t

theorem typedComplexFunction_le_native {n : ℕ}
    (v : DVec (V B) n) (g a : STerm n) :
    bTruth v (typedComplexFunctionOn_f g a) ≤
      graphTypedShape (bTerm v g) (bTerm v a) ⊓
        graphTypedTotalUnique (bTerm v g) (bTerm v a) := by
  unfold typedComplexFunctionOn_f graphTypedShape graphTypedTotalUnique
  simp only [boolean_realize_bounded_formula_and,bTruth_allIn_r181,bTruth_exIn_r181,
    bTruth_sEx_r181,bTruth_sAll_r181,bTruth_equal_r181,bTruth_imp_r181,
    boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    value_f,bTerm_liftOne,bTerm_liftTwo,bTerm_liftThree,bTerm_current_r181]
  have imp_mono_right (a : B) {b c : B} (h : b ≤ c) : imp a b ≤ imp a c := by
    unfold imp
    exact sup_le_sup_left h _
  apply inf_le_inf
  · apply iInf_mono
    intro q
    apply imp_mono_right
    apply iSup_mono
    intro i
    apply inf_le_inf le_rfl
    apply iSup_mono
    intro z
    exact inf_le_inf (bTruth_complex_le_weak _ _) le_rfl
  · apply iInf_mono
    intro i
    apply imp_mono_right
    apply iSup_mono
    intro z
    exact inf_le_inf (bTruth_complex_le_weak _ _) le_rfl

end JSP000930.AnalyticSyntax
