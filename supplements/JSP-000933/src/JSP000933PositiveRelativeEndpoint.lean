import JSP000933ExactGenericGraphOrder

open Fol Lattice Erdos1123
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

theorem positive_forces_densityQuotientIso_r206 :
    (⊤ : PosB) ⊩[V PosB] densityQuotientIso_f := by
  change (⊤ : PosB) ≤ bTruth (DVec.nil : DVec (V PosB) 0) densityQuotientIso_f
  unfold densityQuotientIso_f
  rw [bTruth_sEx_r181]
  apply le_iSup_of_le posGraph
  let v : DVec (V PosB) 1 := DVec.cons posGraph DVec.nil
  let t := x0 0
  have hP : (⊤ : PosB) ≤ bTruth v (pairsOnly_f t) := by
    rw [bTruth_pairsOnly_r205]
    exact generic_graph_pairsOnly_r187 ordinaryBlocks logarithmicBlocks
  have hT : (⊤ : PosB) ≤ bTruth v (graphTotal_f t) := by
    rw [bTruth_graphTotal_r205]
    exact generic_graph_totalSide_r187 ordinaryBlockStructure logarithmicBlockStructure false
  have hO : (⊤ : PosB) ≤ bTruth v (graphOnto_f t) := by
    rw [bTruth_graphOnto_r205]
    exact generic_graph_totalSide_r187 ordinaryBlockStructure logarithmicBlockStructure true
  have hR : (⊤ : PosB) ≤ bTruth v (graphPreserveReflect_f t) :=
    generic_graph_preserveReflect_r205
  change (⊤ : PosB) ≤ bTruth v (bd_and (pairsOnly_f t) (bd_and (graphTotal_f t)
    (bd_and (graphOnto_f t) (graphPreserveReflect_f t))))
  simp only [boolean_realize_bounded_formula_and]
  exact le_inf hP (le_inf hT (le_inf hO hR))

theorem positive_model_ZFC_plus_densityQuotientIso_r206 :
    (⊤ : PosB) ⊩ₜ[V PosB] (insert densityQuotientIso_f ZFC) := by
  unfold Fol.all_forced_in
  apply le_iInf
  intro φ
  apply le_iInf
  intro hφ
  rcases Set.mem_insert_iff.mp hφ with rfl | hφ
  · exact positive_forces_densityQuotientIso_r206
  · have hZ : (⊤ : PosB) ≤ ⨅ f ∈ ZFC, boolean_realize_sentence (S := V PosB) f :=
      bSet_models_ZFC
    exact (hZ.trans (iInf_le _ φ)).trans (iInf_le _ hφ)

theorem positive_ZFC_plus_densityQuotientIso_consistent_r206 :
    SentTheory.is_consistent (insert densityQuotientIso_f ZFC) := by
  letI : Nonempty (V PosB) := ⟨(∅ : bSet PosB)⟩
  exact consis_of_exists_bmodel positive_model_ZFC_plus_densityQuotientIso_r206

theorem positive_relativeConsistency_densityQuotientIso_r206 :
    SentTheory.is_consistent ZFC → SentTheory.is_consistent (insert densityQuotientIso_f ZFC) :=
  fun _ => positive_ZFC_plus_densityQuotientIso_consistent_r206

end SetLanguage
end JSP000933
