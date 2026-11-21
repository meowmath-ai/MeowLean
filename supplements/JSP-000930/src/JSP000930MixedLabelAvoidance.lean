import JSP000933RelativeDiscreteChoices

namespace JSP000930
namespace MixedPalettes

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

abbrev Label (B : Type) [CompleteBooleanAlgebra B] :=
  DiscreteChoiceOn (B := B) OmegaOneIndex (⊤ : B)

theorem exists_complete_partial_label (x : OmegaOneIndex) (w : OmegaOneIndex → B)
    (hW : Pairwise fun i j => Disjoint (w i) (w j)) :
    ∃ T : Label B, ∀ i, w i ≤ T.value i := by
  classical
  let W := ⨆ i, w i
  let v (i : OmegaOneIndex) := if i = x then w i ⊔ Wᶜ else w i
  have leV (i : OmegaOneIndex) : w i ≤ v i := by
    by_cases h : i = x
    · simp only [v, ite_eq_left h]
      exact le_sup_left
    · simp only [v, ite_eq_right h, le_rfl]
  have hDisj (i : OmegaOneIndex) : Disjoint (Wᶜ) (w i) :=
    disjoint_compl_left_iff.mpr (le_iSup w i)
  have hPair : Pairwise fun i j => Disjoint (v i) (v j) := by
    intro i j hi
    by_cases hix : i = x
    · have hjx : j ≠ x := fun h => hi (hix.trans h.symm)
      rw [show v i = w i ⊔ Wᶜ by simp only [v,ite_eq_left hix],
        show v j = w j by simp only [v,ite_eq_right hjx]]
      exact disjoint_sup_left.mpr ⟨hW hi,hDisj j⟩
    · by_cases hjx : j = x
      · rw [show v i = w i by simp only [v,ite_eq_right hix],
          show v j = w j ⊔ Wᶜ by simp only [v,ite_eq_left hjx]]
        exact disjoint_sup_right.mpr ⟨hW hi,(hDisj i).symm⟩
      · simpa only [v,ite_eq_right hix,ite_eq_right hjx] using hW hi
  have hCover : (⨆ i, v i) = (⊤ : B) := by
    apply top_unique
    have h₁ : W ≤ ⨆ i, v i := iSup_le (fun i => (leV i).trans (le_iSup v i))
    have hv : Wᶜ ≤ v x := by
      simp only [v,ite_eq_left rfl]
      exact le_sup_right
    have h₂ : Wᶜ ≤ ⨆ i, v i := hv.trans (le_iSup v x)
    have h : W ⊔ Wᶜ ≤ ⨆ i, v i := sup_le h₁ h₂
    simpa only [sup_compl_eq_top] using h
  exact ⟨⟨v,hPair,(fun _ => le_top),hCover⟩,leV⟩

theorem avoid_countable_labels
    (hB : BoundsCountableOmegaOneNames B)
    {X : Type} {s : Set X} (hs : s.Countable) (hNE : s.Nonempty)
    (T : s → Label B) :
    (⊤ : B) ≤ ⨆ i : OmegaOneIndex, ⨅ d : s, ((T d).value i)ᶜ := by
  obtain ⟨p,hp⟩ := hs.exists_surjective hNE
  let V (n : ℕ) (j : OmegaOneIndex) := (T (p n)).value j
  have hGlobal : (⊤ : B) ≤ ⨅ n, ⨆ j, V n j := by
    apply le_iInf
    intro n
    exact (T (p n)).covers.ge
  apply (hGlobal.trans (hB V)).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply le_iInf
  intro d
  obtain ⟨n,hn⟩ := hp d
  apply (iInf_le (fun n => ⨆ j : {j : OmegaOneIndex // j < i},V n j.1) n).trans
  apply iSup_le
  intro j
  change (T (p n)).value j.1 ≤ ((T d).value i)ᶜ
  rw [hn]
  exact le_compl_iff_disjoint_right.mpr ((T d).disjoint (ne_of_lt j.2))

end MixedPalettes
end JSP000930
