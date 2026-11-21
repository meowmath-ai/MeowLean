import JSP000930NegativeActualFinalKappaRealCover

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes JSP000933.PreparedModel
  JSP000933.ForcingTransport JSP000930.Positive JSP000930.Positive.Cohen JSP000930.SetLanguage

variable {N : Type} {Q : ValuedPoset PreparedBA N}
  [Nonempty (TotalCondition Q)]

theorem bulkEmbedding_gives_final_reals_lower (F : CompleteValueMap WetzelCohenBA (TotalBA Q)) :
    (⊤ : TotalBA Q) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega) := by
  apply checkedKappa_injects_into_named_reals
    (fun i n => F.toFun (cohenRow PreparedBA (Sum.inl i : WetzelRow) n))
  intro i j hij
  rw [← map_realEqValue_r126 F]
  rw [cohen_rows_distinct (fun h => hij (Sum.inl_injective h)),F.map_bot]

theorem prepared_relativeCCC_final_reals_upper [Nonempty N]
    (hQ : ForcesRelativeCCC Q) (hN : Cardinal.mk N ≤ GroundContinuumSucc) :
    (⊤ : TotalBA Q) ≤ injects_into (bv_powerset bSet.omega) (check BaseSuccPSet) := by
  obtain ⟨e,he⟩ := prepared_relativeCCC_kappa_realCover Q hQ hN
  exact named_reals_inject_into_checkedKappa e he

theorem prepared_relativeCCC_boundsOmegaOne (hQ : ForcesRelativeCCC Q) :
    BoundsCountableOmegaOneNames (TotalBA Q) :=
  relativeCCC_preserves_boundsOmegaOne_r436 Q prepared_boundsOmegaOne_r432 hQ

theorem prepared_relativeCCC_boundsKappa (hQ : ForcesRelativeCCC Q) :
    BoundsSmallKappaNames (TotalBA Q) :=
  relativeCCC_preserves_boundsSmallKappa_p10 Q actual_prepared_boundsSmallKappa_r473 hQ

theorem final_relativeCCC_forces_continuumAlephTwo [Nonempty N]
    (hQ : ForcesRelativeCCC Q) (hN : Cardinal.mk N ≤ GroundContinuumSucc)
    (F : CompleteValueMap WetzelCohenBA (TotalBA Q)) :
    (⊤ : TotalBA Q) ⊩[V (TotalBA Q)] continuumAlephTwo_f :=
  forces_continuumAlephTwo_from_prepared (totalBaseMap Q)
    (prepared_relativeCCC_boundsOmegaOne hQ) (prepared_relativeCCC_boundsKappa hQ)
    (prepared_relativeCCC_final_reals_upper hQ hN) (bulkEmbedding_gives_final_reals_lower F)

theorem final_total_forces_ZFC :
    (⊤ : TotalBA Q) ⊩ₜ[V (TotalBA Q)] ZFC :=
  bSet_models_ZFC

end JSP000930.Negative
