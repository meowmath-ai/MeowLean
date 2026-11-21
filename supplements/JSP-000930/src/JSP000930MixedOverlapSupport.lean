import JSP000930MixedPaletteTable

namespace JSP000930
namespace MixedPalettes

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def labelAgreement (U V : Label B) : B :=
  ⨆ y : OmegaOneIndex, U.value y ⊓ V.value y

noncomputable def strictRankEvent (U V : Label B) : B :=
  ⨆ t : OmegaOneIndex, ⨆ c : {c : OmegaOneIndex // c < t}, U.value c.1 ⊓ V.value t

section

variable {I : Type} [LinearOrder I] [WellFoundedLT I]

theorem rows_tail_agreement_bot (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) {a b x : I} (hab : b < a) (hax : a ≤ x) :
    labelAgreement (rows hB R a x) (rows hB R b x) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro y
  exact disjoint_iff_inf_le.mp (rows_tail_disjoint hB R hab hax y)

theorem rows_overlap_le_strict_rank (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) {a b x : I} (hab : b < a) (hxa : x < a) :
    labelAgreement (rows hB R a x) (rows hB R b x) ≤
      strictRankEvent (R.strict a ⟨x,hxa⟩) (R.strict a ⟨b,hab⟩) := by
  let X := R.strict a ⟨x,hxa⟩
  let P := R.strict a ⟨b,hab⟩
  let A := rows hB R a x
  let D := rows hB R b x
  unfold labelAgreement
  apply iSup_le
  intro y
  let m := A.value y ⊓ D.value y
  change m ≤ strictRankEvent X P
  have h₁ : m ≤ ⨆ t, m ⊓ P.value t := by
    rw [← inf_iSup_eq, P.covers, inf_top_eq] <;> exact le_rfl
  apply h₁.trans
  apply iSup_le
  intro t
  let u := m ⊓ P.value t
  have h₂ : u ≤ ⨆ c, u ⊓ X.value c := by
    rw [← inf_iSup_eq, X.covers, inf_top_eq] <;> exact le_rfl
  change u ≤ _
  apply h₂.trans
  apply iSup_le
  intro c
  by_cases h : c < t
  · have hn : u ⊓ X.value c ≤ X.value c ⊓ P.value t :=
      le_inf inf_le_right (inf_le_left.trans inf_le_right)
    exact hn.trans (le_iSup_of_le t (le_iSup
      (fun r : {r : OmegaOneIndex // r<t} => X.value r.1 ⊓ P.value t) ⟨c,h⟩))
  · have hd := rows_avoid_prior_rank hB R hab hxa (le_of_not_gt h) y
    have hA : u ⊓ X.value c ≤ A.value y :=
      inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hD : u ⊓ X.value c ≤ D.value y :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hP : u ⊓ X.value c ≤ P.value t := inf_le_left.trans inf_le_right
    have hlow : u ⊓ X.value c ≤ ⊥ :=
      (le_inf hA (le_inf (le_inf inf_le_right hP) hD)).trans (disjoint_iff_inf_le.mp hd)
    exact hlow.trans bot_le

end

end MixedPalettes
end JSP000930
