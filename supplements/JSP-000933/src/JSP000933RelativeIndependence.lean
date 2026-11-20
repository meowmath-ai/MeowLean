import JSP000933ActualPreparedNamedOCA
import JSP000933ActualFirstOrderNonIso
import JSP000933PositiveRelativeEndpoint

open Fol
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open ForcingTransport

theorem actualPreparedOca_forces_densityQuotientNonIso :
    (⊤ : ActualPreparedOcaBA) ⊩[V ActualPreparedOcaBA] densityQuotientNonIso_f :=
  namedForce_cantorOCA_implies_nonIso_r389
    ActualPreparedOcaBA ⊤ actualPreparedOca_forces_cantorOCA_r498

theorem actualPreparedOca_model_ZFC_plus_densityQuotientNonIso :
    (⊤ : ActualPreparedOcaBA) ⊩ₜ[V ActualPreparedOcaBA]
      (insert densityQuotientNonIso_f ZFC) := by
  unfold Fol.all_forced_in
  apply le_iInf
  intro φ
  apply le_iInf
  intro hφ
  rcases Set.mem_insert_iff.mp hφ with rfl | hφ
  · exact actualPreparedOca_forces_densityQuotientNonIso
  · have hZ : (⊤ : ActualPreparedOcaBA) ≤
        ⨅ f ∈ ZFC, boolean_realize_sentence (S := V ActualPreparedOcaBA) f :=
      bSet_models_ZFC
    exact (hZ.trans (iInf_le _ φ)).trans (iInf_le _ hφ)

theorem actualPreparedOca_ZFC_plus_densityQuotientNonIso_consistent :
    SentTheory.is_consistent (insert densityQuotientNonIso_f ZFC) := by
  letI : Nonempty (V ActualPreparedOcaBA) := ⟨(∅ : bSet ActualPreparedOcaBA)⟩
  exact consis_of_exists_bmodel actualPreparedOca_model_ZFC_plus_densityQuotientNonIso

theorem erdos1123_densityQuotients_relative_independence :
    SentTheory.is_consistent ZFC →
      (SentTheory.is_consistent (insert densityQuotientIso_f ZFC) ∧
       SentTheory.is_consistent (insert densityQuotientNonIso_f ZFC)) :=
  fun hZ => ⟨positive_relativeConsistency_densityQuotientIso_r206 hZ,
    actualPreparedOca_ZFC_plus_densityQuotientNonIso_consistent⟩

end SetLanguage
end JSP000933
