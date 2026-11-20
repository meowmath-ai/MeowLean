import JSP000933RelativeChoiceNormalization

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem relativeCCC_preserves_boundsOmegaOne_r436 (Q : ValuedPoset B N)
    (hB : BoundsCountableOmegaOneNames B) (hQ : ForcesRelativeCCC Q) :
    BoundsCountableOmegaOneNames (TotalBA Q) := by
  intro V
  let C (n : ℕ) := firstChoiceCell (V n)
  let W (n : ℕ) (i : OmegaOneIndex) := supportProjection Q (C n i)
  let F (n : ℕ) (a : OmegaOneIndex) := (aboveValue (W n) a)ᶜ
  have hCovered (n : ℕ) : (⨆ a,F n a)=⊤ := by
    have hh := relativeCCC_projectedAntichain_bounded_r434 Q hQ (C n)
      (fun i j h => firstChoiceCell_disjoint_r435 (V n) i j h)
    have hc := congrArg (fun x : B => xᶜ) hh
    simpa only [unboundedValue,compl_iInf,compl_bot,W,F] using hc
  let G (b : OmegaOneIndex) : B :=
    ⨅ n,⨆ a : {a : OmegaOneIndex // a<b},F n a.val
  have hG : (⨆ b,G b)=⊤ :=
    top_unique ((le_iInf (fun n => (hCovered n).ge)).trans (hB F))
  let m : TotalBA Q := ⨅ n,⨆ i,V n i
  have hM : m≤ m⊓(⨆ b,baseEmbed Q (G b)) := by
    rw [← baseEmbed_joins_r427,hG,baseEmbed_top_r427,inf_top_eq]
  apply hM.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro n
  let t := m⊓baseEmbed Q (G b)
  have hAll : t≤⨆ i,C n i := by
    rw [firstChoiceCell_join_r435]
    exact inf_le_left.trans (iInf_le _ n)
  apply (le_inf le_rfl hAll).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  by_cases hi : i<b
  · exact inf_le_right.trans ((firstChoiceCell_le_r435 (V n) i).trans
      (le_iSup (fun j : {j : OmegaOneIndex // j < b} => V n j.val) ⟨i,hi⟩))
  · have hN : G b≤(W n i)ᶜ := by
      apply (iInf_le _ n).trans
      apply iSup_le
      intro a
      exact compl_le_compl (le_iSup (fun j : {j : OmegaOneIndex // a.val < j} => W n j.val)
        ⟨i,a.property.trans_le (le_of_not_gt hi)⟩)
    have hN' : t≤(baseEmbed Q (W n i))ᶜ :=
      (inf_le_right.trans (baseEmbed_mono_r427 Q hN)).trans_eq (baseEmbed_compl_r427 Q _)
    have hP : C n i≤baseEmbed Q (W n i) :=
      (supportProjection_le_iff_r428 Q _ _).mp le_rfl
    have hs : t⊓C n i≤⊥ := by
      have hd : Disjoint (baseEmbed Q (W n i))ᶜ (baseEmbed Q (W n i)) := disjoint_compl_left
      exact (inf_le_inf hN' hP).trans (disjoint_iff_inf_le.mp hd)
    exact hs.trans bot_le

end RelativeOCA
end JSP000933
