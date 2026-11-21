import JSP000930ConditionalNegativeLiteralConsistency
import JSP000930NegativeLiteralNegativeIterationAssembly

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Consistency

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.PreparedModel
  JSP000933.RelativeOCA JSP000933.ForcingTransport JSP000933.SetLanguage
  JSP000930.Positive.Cohen JSP000930.SetLanguage JSP000930.Negative

theorem literal_hayman_pairs_of_actual_negative_iteration
    {N : Type} [Nonempty N] (Q : ValuedPoset PreparedBA N)
    [Nonempty (TotalCondition Q)] (hQ : ForcesRelativeCCC Q)
    (hN : Cardinal.mk N ≤ GroundContinuumSucc)
    (F : CompleteValueMap WetzelCohenBA (TotalBA Q))
    (S : NamedPaletteSchedule (TotalBA Q)) :
    (SentTheory.is_consistent (insert haymanBound_f ZFC) ∧
     SentTheory.is_consistent (insert (bd_not haymanBound_f) ZFC)) ∧
    (SentTheory.is_consistent (insert haymanBound_f (insert continuumAlephTwo_f ZFC)) ∧
     SentTheory.is_consistent (insert (bd_not haymanBound_f) (insert continuumAlephTwo_f ZFC))) := by
  have hZ : (⊤ : TotalBA Q) ⊩ₜ[V (TotalBA Q)] ZFC :=
    final_total_forces_ZFC
  have hN14 := final_relativeCCC_forces_refutesHaymanAtAlephTwo Q hQ hN F S
  have hn := (haymanLiteral_pair_components continuumAlephTwo_f (bd_not haymanBound_f) hN14).2
  exact ⟨literal_hayman_consistency_pair_of_negative hZ hn,
    literal_hayman_sameContinuum_pair_of_negative hZ hN14⟩

end JSP000930.Consistency
