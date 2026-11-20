import JSP000933BooleanSentenceLanguage
import JSP000933CantorOCASentence
import JSP000933NamedOCATop

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open BooleanNames CantorCodes FiniteSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

@[simp] theorem bTruth_wordCylinder_r182 {n : ℕ} (v : DVec (V B) n) (w A : STerm n) :
    bTruth v (wordCylinder_f w A) = nameWordCylinderValue (bTerm v w) (bTerm v A) := by
  simp only [wordCylinder_f,bTruth_exIn_r181,bTruth_allIn_r181,
    boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_biimp,
    boolean_realize_bounded_term_Powerset',boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_pair',boolean_realize_bounded_formula_mem',
    bTruth_equal_r181,bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,bTerm_up3_r181,
    omega,powerset,mem_powerset_subset_r181,equiv_bitEq_r181,inf_iSup_eq,nameWordCylinderValue,wordAgreementValue]

@[simp] theorem bTruth_openEdge_r182 {n : ℕ} (v : DVec (V B) n) (W A Z : STerm n) :
    bTruth v (openEdge_f W A Z) = namedOpenEdgeValue (bTerm v W) (bTerm v A) (bTerm v Z) := by
  simp only [openEdge_f,bTruth_sEx_r181,bTruth_equal_r181,boolean_realize_bounded_formula_not,
    boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    bTruth_wordCylinder_r182,bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,
    namedOpenEdgeValue,namedRawEdgeValue,symPairMem]

@[simp] theorem bTruth_countableSet_r182 {n : ℕ} (v : DVec (V B) n) (C : STerm n) :
    bTruth v (countableSet_f C) = weakCountabilityValue (bTerm v C) := by
  simp only [countableSet_f,bTruth_sEx_r181,bTruth_allIn_r181,bTruth_exIn_r181,
    boolean_realize_bounded_formula_and,bTruth_imp_r181,bTruth_equal_r181,
    omega,boolean_realize_bounded_term_omega',value_f,boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair',bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,
    bTerm_up3_r181,Lattice.imp_infi_eq,imp_curry_r181,weakCountabilityValue,weakUniqueValue,bSet.is_surj]
  exact congrArg iSup (funext fun f : bSet B => inf_comm _ _)

@[simp] theorem bTruth_openClique_r182 {n : ℕ} (v : DVec (V B) n) (X W C : STerm n) :
    bTruth v (openClique_f X W C) =
      namedCliqueValue (bTerm v X) (bTerm v W) (bTerm v C) := by
  simp only [openClique_f,bTruth_countableSet_r182,bTruth_openEdge_r182,bTruth_allIn_r181,
    boolean_realize_bounded_formula_subset',boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_not,bTruth_imp_r181,bTruth_equal_r181,
    bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,Lattice.imp_infi_eq,
    imp_curry_r181,namedCliqueValue]

@[simp] theorem bTruth_closedCodeAt_r182 {n : ℕ} (v : DVec (V B) n) (H i A : STerm n) :
    bTruth v (closedCodeAt_f H i A) =
      namedSectionClosed (bTerm v H) (bTerm v i) (bTerm v A) := by
  simp only [closedCodeAt_f,bTruth_sAll_r181,bTruth_imp_r181,boolean_realize_bounded_formula_not,
    value_f,boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    bTruth_wordCylinder_r182,bTerm_current_r181,bTerm_up_r181,namedSectionClosed_unfold_r178]

@[simp] theorem bTruth_closedCover_r182 {n : ℕ} (v : DVec (V B) n) (X W H : STerm n) :
    bTruth v (closedIndependentCover_f X W H) =
      namedCoverValue (bTerm v X) (bTerm v W) (bTerm v H) := by
  simp only [closedIndependentCover_f,bTruth_closedCodeAt_r182,bTruth_openEdge_r182,
    bTruth_allIn_r181,bTruth_exIn_r181,boolean_realize_bounded_formula_and,
    bTruth_imp_r181,boolean_realize_bounded_formula_not,omega,boolean_realize_bounded_term_omega',
    bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,bTerm_up3_r181,
    Lattice.imp_infi_eq,imp_curry_r181,namedCoverValue]

theorem bTruth_cantorOCA_eq_r182 :
    boolean_realize_sentence (S := V B) cantorOCA_f = namedCantorOCAValue B := by
  change bTruth (DVec.nil : DVec (V B) 0) cantorOCA_f = _
  simp only [cantorOCA_f,bTruth_sAll_r181,bTruth_sEx_r181,bTruth_imp_r181,
    boolean_realize_bounded_formula_or,boolean_realize_bounded_formula_subset',
    bTruth_openClique_r182,bTruth_closedCover_r182,bTerm_current_r181,bTerm_up_r181,bTerm_up2_r181,
    omegaSubsets,omega,powerset,boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_omega',bSet.subset_unfold',mem_powerset_subset_r181,
    namedAllRealsValue,namedCantorOCAValue]

theorem ocaIteration_forces_cantorOCA_r182 (P : OCAParameters)
    (hDia : DiamondAtOmegaOne P.guess) :
    (⊤ : ocaB P) ⊩[V (ocaB P)] cantorOCA_f := by
  change (⊤ : ocaB P) ≤ boolean_realize_sentence (S := V (ocaB P)) cantorOCA_f
  rw [bTruth_cantorOCA_eq_r182,ocaIteration_namedCantorOCA_top_r180 P hDia]

theorem ocaIteration_ZFC_and_cantorOCA_r182 (P : OCAParameters)
    (hDia : DiamondAtOmegaOne P.guess) :
    ((⊤ : ocaB P) ⊩ₜ[V (ocaB P)] ZFC) ∧ ((⊤ : ocaB P) ⊩[V (ocaB P)] cantorOCA_f) :=
  ⟨bSet_models_ZFC,ocaIteration_forces_cantorOCA_r182 P hDia⟩

end SetLanguage
end JSP000933
