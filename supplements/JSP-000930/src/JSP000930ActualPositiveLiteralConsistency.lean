import JSP000930PositiveClosedPositiveCohenModel

open Fol bSet Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Consistency

open JSP000930.SetLanguage JSP000930.Positive.Cohen JSP000933.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem force_insert_ZFCTheory (T : SentTheory L_ZFC) (φ : sentence L_ZFC)
    (hT : (⊤ : B) ⊩ₜ[V B] T) (hφ : (⊤ : B) ⊩[V B] φ) :
    (⊤ : B) ⊩ₜ[V B] (insert φ T) := by
  unfold Fol.all_forced_in at hT ⊢
  apply le_iInf
  intro ψ
  apply le_iInf
  intro hψ
  rcases Set.mem_insert_iff.mp hψ with rfl | hψ
  · exact hφ
  · exact (hT.trans (iInf_le _ ψ)).trans (iInf_le _ hψ)

theorem consistency_of_forced_ZFCTheory (T : SentTheory L_ZFC)
    (hT : (⊤ : B) ⊩ₜ[V B] T) :
    SentTheory.is_consistent T := by
  letI : Nonempty (V B) := ⟨(∅ : bSet B)⟩
  exact consis_of_exists_bmodel hT

theorem haymanLiteral_pair_components (φ ψ : sentence L_ZFC)
    (h : (⊤ : B) ⊩[V B] bd_and φ ψ) :
    ((⊤ : B) ⊩[V B] φ) ∧ ((⊤ : B) ⊩[V B] ψ) := by
  change (⊤ : B) ≤ bTruth DVec.nil (bd_and φ ψ) at h
  rw [JSP000930.AnalyticSyntax.bTruth_and_eq] at h
  exact ⟨h.trans inf_le_left,h.trans inf_le_right⟩

theorem wetzelCohen_consistent_ZFC_plus_haymanBound :
    SentTheory.is_consistent (insert haymanBound_f ZFC) :=
  consistency_of_forced_ZFCTheory _
    (force_insert_ZFCTheory _ _ wetzelCohen_forces_ZFC wetzelCohen_forces_haymanBound)

theorem wetzelCohen_consistent_ZFC_plus_haymanAtAlephTwo :
    SentTheory.is_consistent (insert haymanAtAlephTwo_f ZFC) :=
  consistency_of_forced_ZFCTheory _
    (force_insert_ZFCTheory _ _ wetzelCohen_forces_ZFC wetzelCohen_forces_haymanAtAlephTwo)

theorem wetzelCohen_consistent_ZFC_plus_alephTwo_plus_haymanBound :
    SentTheory.is_consistent (insert haymanBound_f (insert continuumAlephTwo_f ZFC)) := by
  obtain ⟨hC,hH⟩ := haymanLiteral_pair_components continuumAlephTwo_f haymanBound_f
    wetzelCohen_forces_haymanAtAlephTwo
  exact consistency_of_forced_ZFCTheory _
    (force_insert_ZFCTheory _ _ (force_insert_ZFCTheory _ _ wetzelCohen_forces_ZFC hC) hH)

end JSP000930.Consistency
