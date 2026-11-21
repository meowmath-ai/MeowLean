import JSP000930PositiveInitialCardinalForwardMaps
import JSP000930PositiveNoInjectionCheckedSmall
import JSP000930BooleanCardinalSyntax

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.ForcingTransport
open JSP000930.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedOmegaOne_is_nextInitialCard (hB : BoundsCountableOmegaOneNames B) :
    (⊤ : B) ≤ nextInitialCard bSet.omega (check BaseOmegaOne) := by
  unfold nextInitialCard
  refine le_inf (Ord_card_ex (Cardinal.aleph 1)) (le_inf (le_inf
    omega_injects_into_checkedOmegaOne ?_) ?_)
  · rw [checkedOmegaOne_not_injects_omega hB,compl_bot]
  · apply le_iInf
    intro z
    rw [← _root_.deduction,top_inf_eq]
    exact injects_into_omega_of_mem_aleph_one_check le_rfl

theorem checkedKappa_is_nextInitialCard
    (F : CompleteValueMap PreparedBA B) (hB : BoundsSmallKappaNames B) :
    (⊤ : B) ≤ nextInitialCard (check BaseOmegaOne) (check BaseSuccPSet) := by
  unfold nextInitialCard
  refine le_inf (Ord_card_ex GroundContinuumSucc) (le_inf (le_inf
    checkedOmegaOne_injects_into_kappa ?_) ?_)
  · have hS : Cardinal.mk BaseOmegaOne.Type < GroundContinuumSucc := by
      rw [baseOmegaOne_type_card_r391]
      exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
    rw [checkedSmall_notInject_kappa hB BaseOmegaOne hS,compl_bot]
  · exact (checkedBoundedAll_iff_r418 BaseSuccPSet preparedOrdinalEntry
      preparedKappa_basis_r418 preparedKappa_mem_r418 (⊤ : B)
      (fun z => injects_into z (check BaseOmegaOne)) B_ext_injects_into_left).mpr
        (checked_predecessor_injects_into_omegaOne F)

theorem forces_continuumAlephTwo_from_prepared
    (F : CompleteValueMap PreparedBA B) (h₁ : BoundsCountableOmegaOneNames B)
    (h₂ : BoundsSmallKappaNames B)
    (hUp : (⊤ : B) ≤ injects_into (bv_powerset bSet.omega) (check BaseSuccPSet))
    (hLo : (⊤ : B) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega)) :
    (⊤ : B) ⊩[V B] continuumAlephTwo_f :=
  forces_continuumAlephTwo_f_r6 (checkedOmegaOne_is_nextInitialCard h₁)
    (checkedKappa_is_nextInitialCard F h₂) hLo hUp

namespace Cohen

theorem wetzelCohen_boundsOmegaOne : BoundsCountableOmegaOneNames WetzelCohenBA :=
  relativeCCC_preserves_boundsOmegaOne_r436 wetzelCohenPoset
    prepared_boundsOmegaOne_r432 (cohen_forcesRelativeCCC prepared_boundsOmegaOne_r432)

theorem wetzelCohen_boundsKappa : BoundsSmallKappaNames WetzelCohenBA :=
  relativeCCC_preserves_boundsSmallKappa_p10 wetzelCohenPoset
    actual_prepared_boundsSmallKappa_r473 (cohen_forcesRelativeCCC prepared_boundsOmegaOne_r432)

theorem wetzelCohen_forces_continuumAlephTwo :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] continuumAlephTwo_f :=
  forces_continuumAlephTwo_from_prepared (totalBaseMap wetzelCohenPoset)
    wetzelCohen_boundsOmegaOne wetzelCohen_boundsKappa
    wetzelCohen_reals_inject_into_kappa wetzelCohen_kappa_injects_into_reals

theorem wetzelCohen_forces_ZFC : (⊤ : WetzelCohenBA) ⊩ₜ[V WetzelCohenBA] ZFC :=
  bSet_models_ZFC

end Cohen
end JSP000930.Positive
