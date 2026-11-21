import JSP000930ActualPreparedRanks

namespace JSP000930
namespace MixedPalettes

open Set JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

private theorem ground_Iic_countable_r27 (c : OmegaOneIndex) : (Set.Iic c).Countable := by
  have hC : (Set.Iio c).Countable :=
    Set.countable_coe_iff.mp (OmegaOneIndex_initial_countable_r61 c)
  apply (hC.union (Set.countable_singleton c)).mono
  intro t ht
  change t ≤ c at ht
  rcases lt_or_eq_of_le ht with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

private theorem countable_labels_have_cut
    (hB : BoundsCountableOmegaOneNames B)
    {X : Type} {s : Set X} (hs : s.Countable) (hNE : s.Nonempty) (T : s → Label B) :
    (⊤ : B) ≤ ⨆ b : OmegaOneIndex, ⨅ c : s,
      ⨆ j : {j : OmegaOneIndex // j < b}, (T c).value j.1 := by
  obtain ⟨f,hf⟩ := hs.exists_surjective hNE
  let V (n : ℕ) (i : OmegaOneIndex) := (T (f n)).value i
  have hWhole : (⊤ : B) ≤ ⨅ n, ⨆ i, V n i :=
    le_iInf (fun n => (T (f n)).covers.ge)
  apply (hWhole.trans (hB V)).trans
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro c
  obtain ⟨n,hn⟩ := hf c
  have he : (⨆ i : {i : OmegaOneIndex // i<b},V n i.1) =
      ⨆ i : {i : OmegaOneIndex // i<b}, (T c).value i.1 := by
    unfold V
    rw [hn]
  exact (iInf_le (fun n => ⨆ i : {i : OmegaOneIndex // i<b},V n i.1) n).trans_eq he

private noncomputable def heightPart {J : Type}
    (rank : J → Label B) (height : J → OmegaOneIndex) (c r : OmegaOneIndex) : B :=
  ⨆ j : {j : J // height j = r}, (rank j.1).value c

private theorem heightPart_disjoint {J : Type}
    (rank : J → Label B) (hr : SeparatesRanks rank) (height : J → OmegaOneIndex)
    (c : OmegaOneIndex) :
    Pairwise fun r s => Disjoint (heightPart rank height c r) (heightPart rank height c s) := by
  intro r s hrs
  apply disjoint_iff_inf_le.mpr
  unfold heightPart
  rw [iSup_inf_eq]
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  have he : i.1 ≠ j.1 := by
    intro h
    exact hrs (i.2.symm.trans ((congrArg height h).trans j.2))
  exact disjoint_iff_inf_le.mp (hr i.1 j.1 he c)

open scoped Classical in
theorem mixed_rank_cut_preimages_bounded
    (hB : BoundsCountableOmegaOneNames B)
    {J : Type} (rank : J → Label B) (hr : SeparatesRanks rank)
    (height : J → OmegaOneIndex) (cut : OmegaOneIndex) :
    (⊤ : B) ≤ ⨆ b : OmegaOneIndex, ⨅ j : J, ⨅ c : Set.Iic cut,
      (if height j < b then ⊤ else ((rank j).value c.1)ᶜ) := by
  classical
  have hComp (c : Set.Iic cut) :
      ∃ T : Label B, ∀ r, heightPart rank height c.1 r ≤ T.value r :=
    exists_complete_partial_label cut (heightPart rank height c.1)
      (heightPart_disjoint rank hr height c.1)
  choose T hT using hComp
  apply (countable_labels_have_cut hB (ground_Iic_countable_r27 cut) ⟨cut, Set.mem_Iic.mpr le_rfl⟩ T).trans
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro j
  apply le_iInf
  intro c
  by_cases h : height j < b
  · rw [ite_eq_left h]
    exact le_top
  · rw [ite_eq_right h]
    apply (iInf_le (fun d : Set.Iic cut =>
      ⨆ i : {i : OmegaOneIndex // i<b}, (T d).value i.1) c).trans
    apply iSup_le
    intro i
    have hNe : i.1 ≠ height j := fun he => h (he ▸ i.2)
    have hrj : (rank j).value c.1 ≤ (T c).value (height j) :=
      (le_iSup (fun j' : {j' : J // height j' = height j} => (rank j'.1).value c.1)
        ⟨j,rfl⟩).trans (hT c (height j))
    exact le_compl_iff_disjoint_right.mpr (((T c).disjoint hNe).mono_right hrj)

end MixedPalettes
end JSP000930
