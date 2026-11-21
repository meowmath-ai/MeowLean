import JSP000930FiniteCofinalPairCuts
import JSP000933PreparedPrefixCHRealCodes

namespace JSP000930
namespace MixedPalettes

open JSP000933.PreparedModel JSP000933.RelativeOCA JSP000933.OpenGraphForcing
  JSP000933.BooleanNames JSP000933.BooleanCompletion JSP000933.ForcingTransport

noncomputable def preparedIdentityValues : CompleteValueMap PreparedBA PreparedBA where
  toFun := id
  injective := Function.injective_id
  monotone := fun _ _ h => h
  map_bot := rfl
  map_top := rfl
  map_compl := fun _ => rfl
  map_inf := fun _ _ => rfl
  map_iSup := fun _ => rfl
  map_iInf := fun _ => rfl

noncomputable def preparedWetzelRows :
    GroundContinuumSuccIndex → GroundContinuumSuccIndex → Label PreparedBA :=
  rows prepared_boundsOmegaOne_r432 (preparedRankSystem preparedIdentityValues)

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def transportLabel (F : CompleteValueMap B C) (P : Label B) : Label C where
  value := fun i => F.toFun (P.value i)
  disjoint := by
    intro i j h
    apply disjoint_iff_inf_le.mpr
    rw [← F.map_inf, ← F.map_bot]
    exact F.monotone (disjoint_iff_inf_le.mp (P.disjoint h))
  each_le := fun _ => le_top
  covers := by
    calc
      (⨆ i, F.toFun (P.value i)) = F.toFun (⨆ i, P.value i) := (F.map_iSup P.value).symm
      _ = ⊤ := by rw [P.covers,F.map_top]

theorem labelAgreement_transport (F : CompleteValueMap B C) (P Q : Label B) :
    labelAgreement (transportLabel F P) (transportLabel F Q) =
      F.toFun (labelAgreement P Q) := by
  unfold labelAgreement
  rw [F.map_iSup]
  apply iSup_congr
  intro i
  exact (F.map_inf (P.value i) (Q.value i)).symm

open scoped Classical in
theorem prepared_palette_separates_finite_pairs
    {J : Set GroundContinuumSuccIndex}
    (cofinal : OmegaOneIndex → GroundContinuumSuccIndex) (hMono : Monotone cofinal)
    (hCof : ∀ x : J, ∃ d, x.1 < cofinal d)
    (S : Finset (GroundContinuumSuccIndex × GroundContinuumSuccIndex))
    (hS : ∀ p ∈ S, p.2 < p.1) :
    (⊤ : PreparedBA) ≤ ⨆ d : OmegaOneIndex, ⨅ x : J, ⨅ p : S,
      if cofinal d ≤ x.1 then
        (labelAgreement (preparedWetzelRows p.1.1 x.1)
          (preparedWetzelRows p.1.2 x.1))ᶜ else ⊤ :=
  finite_pairs_separate_on_cofinal_tail prepared_boundsOmegaOne_r432
    (preparedRankSystem preparedIdentityValues) cofinal hMono hCof S hS

end MixedPalettes
end JSP000930
