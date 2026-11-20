import JSP000933ActualFinitePackingContradiction
import JSP000933BooleanFirstOrderOCA

open Fol
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes FiniteSupport

theorem namedOCA_le_actualNonIso_r389
    (B : Type) [NontrivialCompleteBooleanAlgebra B] :
    namedCantorOCAValue B≤(actualIsoValue B)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  let p := namedCantorOCAValue B⊓actualIsoValue B
  change p≤⊥
  by_contra hn
  have hp : p≠⊥ := fun he => hn he.le
  let value (G : bSet B) := graphPairsOnlyValue G ⊓ (graphTotalSideValue G false ⊓
    (graphTotalSideValue G true ⊓ actualPreserveReflectValue G))
  have hSup : p ≤ ⨆ G, value G := (show p ≤ actualIsoValue B from inf_le_right)
  have hExists : ∃ G, p ⊓ value G ≠ ⊥ := by
    by_contra h
    apply hp
    refine le_bot_iff.mp ((le_inf le_rfl hSup).trans ?_)
    rw [inf_iSup_eq]
    exact iSup_le (fun G => (not_ne_iff.mp (fun hG => h ⟨G, hG⟩)).le)
  obtain ⟨G, hq⟩ := hExists
  let q := p ⊓ value G
  have hqp : q ≤ p := inf_le_left
  have hG : q ≤ value G := inf_le_right
  obtain ⟨F,hF,_,hGraph,_⟩ := actualGraph_has_exactCoherentIso_r310 q G hG
  have hO : q≤namedCantorOCAValue B := hqp.trans inf_le_left
  have hPR : q≤actualPreserveReflectValue G := hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  obtain ⟨a,L,hA,hC,hL⟩ := exists_actualWholeBlock_continuousLift_r346 G F hF hO hPR hGraph
  exact hq (actualExactBlockLift_impossible_r388 F a L hC hL hA)

theorem bTruth_cantorOCA_le_nonIso_r389
    (B : Type) [NontrivialCompleteBooleanAlgebra B] :
    boolean_realize_sentence (S := V B) cantorOCA_f≤
      boolean_realize_sentence (S := V B) densityQuotientNonIso_f := by
  rw [bTruth_cantorOCA_eq_r182,bTruth_actualNonIso_r213]
  exact namedOCA_le_actualNonIso_r389 B

theorem namedForce_cantorOCA_implies_nonIso_r389
    (B : Type) [NontrivialCompleteBooleanAlgebra B] (p : B)
    (h : p ⊩[V B] cantorOCA_f) : p ⊩[V B] densityQuotientNonIso_f :=
  h.trans (bTruth_cantorOCA_le_nonIso_r389 B)

theorem negative_ZFC_model_given_native_CHdiamond_r389
    (P : OCAParameters) (hD : DiamondAtOmegaOne P.guess) :
    (⊤ : ocaB P) ⊩ₜ[V (ocaB P)] (insert densityQuotientNonIso_f ZFC) := by
  have H := ocaIteration_ZFC_and_cantorOCA_r182 P hD
  have hNon : (⊤ : ocaB P) ⊩[V (ocaB P)] densityQuotientNonIso_f :=
    namedForce_cantorOCA_implies_nonIso_r389 _ _ H.2
  unfold Fol.all_forced_in
  apply le_iInf
  intro φ
  apply le_iInf
  intro hφ
  rcases Set.mem_insert_iff.mp hφ with rfl | hφ
  · exact hNon
  · have hZ : (⊤ : ocaB P)≤⨅ f ∈ ZFC, boolean_realize_sentence (S := V (ocaB P)) f := H.1
    exact (hZ.trans (iInf_le _ φ)).trans (iInf_le _ hφ)

theorem negative_consistent_given_native_CHdiamond_r389
    (P : OCAParameters) (hD : DiamondAtOmegaOne P.guess) :
    SentTheory.is_consistent (insert densityQuotientNonIso_f ZFC) := by
  letI : Nonempty (V (ocaB P)) := ⟨(∅ : bSet (ocaB P))⟩
  exact consis_of_exists_bmodel (negative_ZFC_model_given_native_CHdiamond_r389 P hD)

end SetLanguage
end JSP000933
