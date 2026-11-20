import JSP000933PreparedActualClubs
import JSP000933BooleanFunctionalGraphs

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanNames

noncomputable def actualGuessWeight (d i : GroundContinuumSuccIndex) : PreparedBA :=
  if i<d then decodePreparedGuess d i else ⊥

noncomputable def actualGuessAt (d : GroundContinuumSuccIndex) : bSet PreparedBA :=
  familyName preparedOrdinalEntry (actualGuessWeight d)

noncomputable def actualGuesses : bSet PreparedBA :=
  functionalGraphName preparedOrdinalEntry actualGuessAt

theorem actualGuess_mem_of_lt_r420 {d i : GroundContinuumSuccIndex} (hi : i<d) :
    ((preparedOrdinalEntry i : bSet PreparedBA)∈ᴮ actualGuessAt d)=decodePreparedGuess d i := by
  rw [actualGuessAt,mem_familyName_self_r70 _ (fun _ _ h => preparedOrdinalEntry_eq_bot_r416 h),
    actualGuessWeight,ite_eq_left hi]

theorem actualGuess_subset_r420 (d : GroundContinuumSuccIndex) :
    (⊤ : PreparedBA)≤actualGuessAt d⊆ᴮ preparedOrdinalEntry d := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction,top_inf_eq,actualGuessAt,mem_familyName_r70]
  apply iSup_le
  intro i
  by_cases hi : i<d
  · exact subst_congr_mem_left' (inf_le_right.trans_eq bv_eq_symm)
      (le_top.trans (preparedEntry_mem_top_r418 hi))
  · rw [actualGuessWeight,ite_eq_right hi,bot_inf_eq]
    exact bot_le

theorem actualGuess_subsetKappa_r420 (d : GroundContinuumSuccIndex) :
    (⊤ : PreparedBA)≤actualGuessAt d⊆ᴮ check BaseSuccPSet := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction,top_inf_eq,actualGuessAt,mem_familyName_r70]
  apply iSup_le
  intro i
  exact subst_congr_mem_left' (inf_le_right.trans_eq bv_eq_symm) (le_top.trans (preparedKappa_mem_r418 i))

theorem actualGuesses_func_r420 :
    (⊤ : PreparedBA)≤ is_func' (check BaseSuccPSet) (bv_powerset (check BaseSuccPSet)) actualGuesses := by
  apply le_inf
  · exact functionValue_functionalGraph_r102 _ _ (fun _ _ h => preparedOrdinalEntry_eq_bot_r416 h)
  · change (⊤ : PreparedBA)≤⨅ x : bSet PreparedBA,(x∈ᴮ check BaseSuccPSet)⟹
        (⨆ y : bSet PreparedBA,(y∈ᴮ bv_powerset (check BaseSuccPSet))⊓(pair x y∈ᴮ actualGuesses))
    apply (checkedBoundedAll_iff_r418 BaseSuccPSet preparedOrdinalEntry preparedKappa_basis_r418
      preparedKappa_mem_r418 ⊤ _ (B_ext_iSup (h := fun y => B_ext_inf B_ext_const
        B_ext_pair_mem_left))).mpr
    intro i
    exact le_iSup_of_le (actualGuessAt i)
      (le_inf (bv_powerset_spec.mp (actualGuess_subsetKappa_r420 i))
        (pair_mem_functionalGraph_self_r102 _ _ i))

noncomputable def actualPrefixAgreement (a g d : bSet PreparedBA) : PreparedBA :=
  ⨅ x : bSet PreparedBA,(x∈ᴮ d)⟹
    (((x∈ᴮ a)⟹(x∈ᴮ g))⊓((x∈ᴮ g)⟹(x∈ᴮ a)))

theorem flypitchImp_eq_himp_r420 (a b : PreparedBA) : (a⟹b)=(a⇨b) := by
  exact le_antisymm (le_himp_iff.mpr (_root_.deduction.mpr le_rfl))
    (_root_.deduction.mp (le_himp_iff.mp le_rfl))

theorem actualPrefixAgreement_of_bits_r420 (a : bSet PreparedBA)
    (d : GroundContinuumSuccIndex) (m : PreparedBA)
    (hm : ∀ i<d,m≤booleanAgree (preparedProfile a i) (decodePreparedGuess d i)) :
    m≤actualPrefixAgreement a (actualGuessAt d) (preparedOrdinalEntry d) := by
  unfold actualPrefixAgreement
  rw [preparedOrdinalEntry_asOrdinal_r416 d]
  let F (x : bSet PreparedBA) :=
    (((x∈ᴮ a)⟹(x∈ᴮ actualGuessAt d))⊓((x∈ᴮ actualGuessAt d)⟹(x∈ᴮ a)))
  have hF : B_ext F := B_ext_inf
    (B_ext_imp (h₁ := B_ext_mem_left) (h₂ := B_ext_mem_left))
    (B_ext_imp (h₁ := B_ext_mem_left) (h₂ := B_ext_mem_left))
  apply (checkedBoundedAll_iff_r418 (PSet.ordinalMk (continuumSuccOrdinal d))
    (fun i : ↥(Set.Iio d) => preparedOrdinalEntry i.val) (preparedEntry_basis_r418 d)
    (fun i => by
      rw [← preparedOrdinalEntry_asOrdinal_r416 d]
      exact preparedEntry_mem_top_r418 i.property) m F hF).mpr
  intro i
  simpa only [F,actualGuess_mem_of_lt_r420 i.property,booleanAgree,preparedProfile,
    flypitchImp_eq_himp_r420] using hm i.val i.property

end PreparedModel
end JSP000933
