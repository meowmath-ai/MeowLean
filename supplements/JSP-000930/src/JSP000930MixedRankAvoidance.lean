import JSP000930MixedLabelAvoidance

namespace JSP000930
namespace MixedPalettes

open Set JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def SeparatesRanks {J : Type} (rank : J → Label B) : Prop :=
  ∀ i j : J, i ≠ j → ∀ c : OmegaOneIndex,
    Disjoint ((rank i).value c) ((rank j).value c)

private noncomputable def rankValue {J : Type} (rank prior : J → Label B)
    (t y : OmegaOneIndex) : B :=
  ⨆ j : J, (rank j).value t ⊓ (prior j).value y

private theorem rankValue_disjoint {J : Type} (rank prior : J → Label B)
    (hR : SeparatesRanks rank) (t : OmegaOneIndex) :
    Pairwise fun y z => Disjoint (rankValue rank prior t y) (rankValue rank prior t z) := by
  intro y z hYZ
  apply disjoint_iff_inf_le.mpr
  unfold rankValue
  rw [iSup_inf_eq]
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  by_cases h : i = j
  · subst j
    exact (inf_le_inf inf_le_right inf_le_right).trans
      (disjoint_iff_inf_le.mp ((prior i).disjoint hYZ))
  · exact (inf_le_inf inf_le_left inf_le_left).trans (disjoint_iff_inf_le.mp (hR i j h t))

private theorem ground_Iic_countable (c : OmegaOneIndex) : (Set.Iic c).Countable := by
  have hC : (Set.Iio c).Countable :=
    Set.countable_coe_iff.mp (OmegaOneIndex_initial_countable_r61 c)
  apply (hC.union (Set.countable_singleton c)).mono
  intro t ht
  change t ≤ c at ht
  rcases lt_or_eq_of_le ht with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

theorem choose_label_avoiding_mixed_rank_cut
    (hB : BoundsCountableOmegaOneNames B)
    {J : Type} (rank prior : J → Label B) (hR : SeparatesRanks rank)
    (current : Label B) :
    ∃ T : Label B, ∀ j : J, ∀ {t c : OmegaOneIndex}, t ≤ c → ∀ y : OmegaOneIndex,
      Disjoint (T.value y)
        (current.value c ⊓ (rank j).value t ⊓ (prior j).value y) := by
  classical
  have hPartial (t : OmegaOneIndex) :
      ∃ V : Label B, ∀ y, rankValue rank prior t y ≤ V.value y :=
    exists_complete_partial_label t (rankValue rank prior t) (rankValue_disjoint rank prior hR t)
  choose V hV using hPartial
  let safe (c y : OmegaOneIndex) : B :=
    ⨅ t : Set.Iic c, ((V t.1).value y)ᶜ
  have hSafe (c : OmegaOneIndex) : (⊤ : B) ≤ ⨆ y, safe c y :=
    avoid_countable_labels hB (ground_Iic_countable c) ⟨c, show c ∈ Set.Iic c from Set.mem_Iic.mpr le_rfl⟩ (fun t => V t.1)
  let U (y : OmegaOneIndex) : B := ⨆ c, current.value c ⊓ safe c y
  have hU : (⊤ : B) ≤ ⨆ y, U y := by
    rw [← current.covers]
    apply iSup_le
    intro c
    calc
      current.value c = current.value c ⊓ (⊤ : B) := by rw [inf_top_eq]
      _ ≤ current.value c ⊓ (⨆ y, safe c y) := inf_le_inf le_rfl (hSafe c)
      _ = ⨆ y, current.value c ⊓ safe c y := inf_iSup_eq _ _
      _ ≤ ⨆ y, U y := iSup_le (fun y => le_iSup_of_le y (le_iSup (fun d => current.value d ⊓ safe d y) c))
  obtain ⟨T, hT⟩ := exists_discreteChoiceOn_r445 (⊤ : B) U hU
  refine ⟨T, ?_⟩
  intro j t c ht y
  let v := current.value c ⊓ (rank j).value t ⊓ (prior j).value y
  apply disjoint_iff_inf_le.mpr
  apply (inf_le_inf (hT y) le_rfl).trans
  change (⨆ c', current.value c' ⊓ safe c' y) ⊓ v ≤ ⊥
  rw [iSup_inf_eq]
  apply iSup_le
  intro c'
  by_cases he : c' = c
  · subst c'
    have hv : v ≤ (V t).value y := by
      apply (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      exact (le_iSup (fun i => (rank i).value t ⊓ (prior i).value y) j).trans (hV t y)
    have hw : current.value c ⊓ safe c y ≤ ((V t).value y)ᶜ := by
      exact inf_le_right.trans (iInf_le (fun r : Set.Iic c => ((V r.1).value y)ᶜ)
        (⟨t, ht⟩ : Set.Iic c))
    exact disjoint_iff_inf_le.mp
      ((disjoint_compl_left_iff.mpr (le_rfl : (V t).value y ≤ (V t).value y)).mono hw hv)
  · have hv : v ≤ current.value c := inf_le_left.trans inf_le_left
    exact disjoint_iff_inf_le.mp ((current.disjoint he).mono inf_le_left hv)

end MixedPalettes
end JSP000930
