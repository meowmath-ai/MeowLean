import JSP000930ActualPositiveLiteralConsistency

open Fol bSet Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Consistency

open JSP000930.SetLanguage JSP000933.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem haymanRefutation_is_literal_negation :
    haymanRefutation_f = bd_not haymanBound_f := rfl

theorem literal_hayman_consistency_pair_of_negative
    (hZ : (⊤ : B) ⊩ₜ[V B] ZFC)
    (hNeg : (⊤ : B) ⊩[V B] bd_not haymanBound_f) :
    SentTheory.is_consistent (insert haymanBound_f ZFC) ∧
    SentTheory.is_consistent (insert (bd_not haymanBound_f) ZFC) :=
  ⟨wetzelCohen_consistent_ZFC_plus_haymanBound,
    consistency_of_forced_ZFCTheory _ (force_insert_ZFCTheory _ _ hZ hNeg)⟩

theorem literal_hayman_sameContinuum_pair_of_negative
    (hZ : (⊤ : B) ⊩ₜ[V B] ZFC)
    (hNeg : (⊤ : B) ⊩[V B] refutesHaymanAtAlephTwo_f) :
    SentTheory.is_consistent (insert haymanBound_f (insert continuumAlephTwo_f ZFC)) ∧
    SentTheory.is_consistent (insert (bd_not haymanBound_f) (insert continuumAlephTwo_f ZFC)) := by
  obtain ⟨hC,hH⟩ := haymanLiteral_pair_components continuumAlephTwo_f (bd_not haymanBound_f) hNeg
  exact ⟨wetzelCohen_consistent_ZFC_plus_alephTwo_plus_haymanBound,
    consistency_of_forced_ZFCTheory _
      (force_insert_ZFCTheory _ _ (force_insert_ZFCTheory _ _ hZ hC) hH)⟩

theorem literal_hayman_conjunction_pair_of_negative
    (hZ : (⊤ : B) ⊩ₜ[V B] ZFC)
    (hNeg : (⊤ : B) ⊩[V B] refutesHaymanAtAlephTwo_f) :
    SentTheory.is_consistent (insert haymanAtAlephTwo_f ZFC) ∧
    SentTheory.is_consistent (insert refutesHaymanAtAlephTwo_f ZFC) :=
  ⟨wetzelCohen_consistent_ZFC_plus_haymanAtAlephTwo,
    consistency_of_forced_ZFCTheory _ (force_insert_ZFCTheory _ _ hZ hNeg)⟩

end JSP000930.Consistency
