import JSP000930NegativeLiteralHaymanRefutation

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.PreparedModel
  JSP000933.RelativeOCA JSP000933.ForcingTransport JSP000933.SetLanguage
  JSP000930.Positive.Cohen JSP000930.SetLanguage

theorem final_relativeCCC_forces_refutesHaymanAtAlephTwo
    {N : Type} [Nonempty N] (Q : ValuedPoset PreparedBA N)
    [Nonempty (TotalCondition Q)] (hQ : ForcesRelativeCCC Q)
    (hN : Cardinal.mk N ≤ GroundContinuumSucc)
    (F : CompleteValueMap WetzelCohenBA (TotalBA Q))
    (S : NamedPaletteSchedule (TotalBA Q)) :
    (⊤ : TotalBA Q) ⊩[V (TotalBA Q)] refutesHaymanAtAlephTwo_f := by
  change (⊤ : TotalBA Q) ≤ bTruth DVec.nil (bd_and continuumAlephTwo_f haymanRefutation_f)
  rw [JSP000930.AnalyticSyntax.bTruth_and_eq]
  exact le_inf (final_relativeCCC_forces_continuumAlephTwo hQ hN F)
    (S.forces_haymanRefutation (JSP000930.Positive.totalBaseMap Q)
      (prepared_relativeCCC_boundsOmegaOne hQ) (prepared_relativeCCC_boundsKappa hQ)
      (bulkEmbedding_gives_final_reals_lower F))

end JSP000930.Negative
