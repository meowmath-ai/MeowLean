import JSP000930MixedRankPreimageBound
import JSP000930MixedOverlapSupport

namespace JSP000930
namespace MixedPalettes

open Set JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]
variable {I : Type} [LinearOrder I] [WellFoundedLT I]

noncomputable def agreementCut
    (hB : BoundsCountableOmegaOneNames B) (R : RankSystem I B)
    (a b : I) {J : Set I} (height : J → OmegaOneIndex) (d : OmegaOneIndex) : B := by
  classical
  exact ⨅ x : J, if height x < d then ⊤ else
    (labelAgreement (rows hB R a x.1) (rows hB R b x.1))ᶜ

theorem agreementCut_mono
    (hB : BoundsCountableOmegaOneNames B) (R : RankSystem I B)
    (a b : I) {J : Set I} (height : J → OmegaOneIndex) :
    Monotone (agreementCut hB R a b height) := by
  classical
  intro d e h
  unfold agreementCut
  apply le_iInf
  intro x
  apply (iInf_le _ x).trans
  by_cases hx : height x < d
  · rw [ite_eq_left hx, ite_eq_left (hx.trans_le h)] <;> exact le_rfl
  · by_cases hx' : height x < e
    · simp only [ite_eq_left hx', le_top]
    · simp only [ite_eq_right hx, ite_eq_right hx', le_rfl]

theorem pair_overlap_has_mixed_height_cut
    (hB : BoundsCountableOmegaOneNames B) (R : RankSystem I B)
    {a b : I} (hba : b < a) {J : Set I} (height : J → OmegaOneIndex) :
    (⊤ : B) ≤ ⨆ d : OmegaOneIndex, agreementCut hB R a b height d := by
  classical
  let IX := {x : J // x.1 < a}
  let rank (x : IX) : Label B := R.strict a ⟨x.1.1, x.2⟩
  have hRank : SeparatesRanks rank := by
    intro x y hxy t
    apply R.strict_separates a _ _ _ t
    intro he
    exact hxy (Subtype.ext (Subtype.ext (congrArg (fun z : {x : I // x < a} => z.val) he)))
  let hgt (x : IX) := height x.1
  let A := R.strict a ⟨b,hba⟩
  let safe (t d : OmegaOneIndex) : B :=
    ⨅ x : IX, ⨅ c : Set.Iic t, if hgt x < d then ⊤ else ((rank x).value c.1)ᶜ
  have hSafe (t : OmegaOneIndex) : (⊤ : B) ≤ ⨆ d, safe t d :=
    mixed_rank_cut_preimages_bounded hB rank hRank hgt t
  rw [← A.covers]
  apply iSup_le
  intro t
  apply (le_inf le_rfl (le_top.trans (hSafe t))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro d
  apply le_iSup_of_le d
  unfold agreementCut
  apply le_iInf
  intro x
  by_cases hD : height x < d
  · rw [ite_eq_left hD]
    exact le_top
  · rw [ite_eq_right hD]
    by_cases hX : x.1 < a
    · let y : IX := ⟨x,hX⟩
      have hBad := rows_overlap_le_strict_rank hB R hba hX
      apply le_compl_iff_disjoint_right.mpr
      apply disjoint_iff_inf_le.mpr
      apply (inf_le_inf le_rfl hBad).trans
      unfold strictRankEvent
      rw [inf_iSup_eq]
      apply iSup_le
      intro t'
      rw [inf_iSup_eq]
      apply iSup_le
      intro c
      by_cases hT : t' = t
      · subst t'
        have hC : safe t d ≤ ((rank y).value c.1)ᶜ := by
          apply (iInf_le _ y).trans
          apply (iInf_le _ (⟨c.1, c.2.le⟩ : Set.Iic t)).trans_eq
          rw [ite_eq_right (show ¬ hgt y < d from hD)]
        exact disjoint_iff_inf_le.mp
          ((disjoint_compl_left_iff.mpr (le_rfl : (rank y).value c.1 ≤ (rank y).value c.1)).mono
            (inf_le_right.trans hC) inf_le_left)
      · exact disjoint_iff_inf_le.mp ((A.disjoint (Ne.symm hT)).mono inf_le_left inf_le_right)
    · rw [rows_tail_agreement_bot hB R hba (le_of_not_gt hX), compl_bot]
      exact le_top

end MixedPalettes
end JSP000930
