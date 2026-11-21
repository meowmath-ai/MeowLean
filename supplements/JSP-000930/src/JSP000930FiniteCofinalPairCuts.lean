import JSP000930MixedPairOverlapCut

namespace JSP000930
namespace MixedPalettes

open Set JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]
variable {I : Type} [LinearOrder I] [WellFoundedLT I]

private theorem finite_mono_cuts {D E : Type} [LinearOrder E] [Nonempty E]
    (S : Finset D) (F : D → E → B)
    (hMono : ∀ j ∈ S, Monotone (F j))
    (hCover : ∀ j ∈ S, (⊤ : B) ≤ ⨆ d, F j d) :
    (⊤ : B) ≤ ⨆ d : E, S.inf (fun j => F j d) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    let d : E := Classical.choice ‹Nonempty E›
    exact le_iSup_of_le d (by simp only [Finset.inf_empty, le_rfl])
  | @insert x S hx ih =>
    have hTop : (⊤ : B) ≤ (⨆ d, F x d) ⊓ (⨆ d : E, S.inf (fun j => F j d)) :=
      le_inf (hCover x (Finset.mem_insert_self _ _))
        (ih (fun j hj => hMono j (Finset.mem_insert_of_mem hj))
          (fun j hj => hCover j (Finset.mem_insert_of_mem hj)))
    apply hTop.trans
    rw [iSup_inf_eq]
    apply iSup_le
    intro d
    rw [inf_iSup_eq]
    apply iSup_le
    intro e
    apply le_iSup_of_le (max d e)
    rw [Finset.inf_insert]
    exact inf_le_inf (hMono x (Finset.mem_insert_self _ _) (le_max_left _ _))
      (Finset.inf_mono_fun (fun j hj =>
        hMono j (Finset.mem_insert_of_mem hj) (le_max_right _ _)))

theorem finite_pairs_have_mixed_height_cut
    (hB : BoundsCountableOmegaOneNames B) (R : RankSystem I B)
    {J : Set I} (height : J → OmegaOneIndex) (S : Finset (I × I))
    (hS : ∀ p ∈ S, p.2 < p.1) :
    (⊤ : B) ≤ ⨆ d : OmegaOneIndex,
      S.inf (fun p => agreementCut hB R p.1 p.2 height d) := by
  letI : Nonempty OmegaOneIndex :=
    Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
  exact finite_mono_cuts S (fun p => agreementCut hB R p.1 p.2 height)
    (fun p _ => agreementCut_mono hB R p.1 p.2 height)
    (fun p hp => pair_overlap_has_mixed_height_cut hB R (hS p hp) height)

open scoped Classical in
theorem finite_pairs_separate_on_cofinal_tail
    (hB : BoundsCountableOmegaOneNames B) (R : RankSystem I B)
    {J : Set I} (cofinal : OmegaOneIndex → I) (hMono : Monotone cofinal)
    (hCof : ∀ x : J, ∃ d, x.1 < cofinal d)
    (S : Finset (I × I)) (hS : ∀ p ∈ S, p.2 < p.1) :
    (⊤ : B) ≤ ⨆ d : OmegaOneIndex, ⨅ x : J, ⨅ p : S,
      if cofinal d ≤ x.1 then
        (labelAgreement (rows hB R p.1.1 x.1) (rows hB R p.1.2 x.1))ᶜ
      else ⊤ := by
  classical
  choose height hHeight using hCof
  apply (finite_pairs_have_mixed_height_cut hB R height S hS).trans
  apply iSup_le
  intro d
  apply le_iSup_of_le d
  apply le_iInf
  intro x
  apply le_iInf
  intro p
  by_cases hd : cofinal d ≤ x.1
  · rw [ite_eq_left hd]
    have hH : ¬ height x < d := by
      intro he
      exact (hHeight x).not_ge ((hMono he.le).trans hd)
    apply (Finset.inf_le (s := S) (f := fun p => agreementCut hB R p.1 p.2 height d) p.2).trans
    unfold agreementCut
    exact (iInf_le _ x).trans_eq (ite_eq_right hH)
  · rw [ite_eq_right hd]
    exact le_top

end MixedPalettes
end JSP000930
