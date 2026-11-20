import JSP000933RelativeOmegaOnePreservation

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem relativeCCC_unbounded_support_r438 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (m : B) (g : OmegaOneIndex→TotalBA Q)
    (hG : ∀ i,m ≤ supportProjection Q (g i)) :
    m ≤ supportProjection Q (unboundedValue g) := by
  classical
  let v := unboundedValue g
  let m0 := m⊓(supportProjection Q v)ᶜ
  change m ≤ supportProjection Q v
  by_contra hn
  have hM : m0≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  let V (a : OmegaOneIndex) := (aboveValue g a)ᶜ
  let C := firstChoiceCell V
  let W (a : OmegaOneIndex) := supportProjection Q (C a)
  let F (b : OmegaOneIndex) := (aboveValue W b)ᶜ
  have hCV : (⨆ a,C a)=vᶜ := by
    rw [firstChoiceCell_join_r435]
    change (⨆ a, (aboveValue g a)ᶜ) = (unboundedValue g)ᶜ
    rw [unboundedValue, compl_iInf]
  have hF : (⨆ b,F b)=⊤ := by
    have hh := relativeCCC_projectedAntichain_bounded_r434 Q hQ C
      (fun i j h => firstChoiceCell_disjoint_r435 V i j h)
    have hc := congrArg (fun z : B => zᶜ) hh
    simpa only [unboundedValue,W,F,compl_iInf,compl_bot] using hc
  have h0 : baseEmbed Q m0≤vᶜ := by
    apply (baseEmbed_mono_r427 Q (show m0≤(supportProjection Q v)ᶜ from inf_le_right)).trans
    rw [baseEmbed_compl_r427]
    exact compl_le_compl ((supportProjection_le_iff_r428 Q _ _).mp le_rfl)
  have hSome : ∃ b,m0⊓F b≠⊥ := by
    by_contra he
    have hz (b : OmegaOneIndex) : m0⊓F b=⊥ := by
      by_contra hb
      exact he ⟨b,hb⟩
    apply hM
    calc
      m0 = m0⊓(⨆ b,F b) := by rw [hF,inf_top_eq]
      _ = ⨆ b,m0⊓F b := inf_iSup_eq _ _
      _ = ⊥ := by simp only [hz,iSup_bot]
  obtain ⟨b,hb⟩ := hSome
  let t := m0⊓F b
  have ht : t≠⊥ := hb
  have hAll : baseEmbed Q t≤⨆ a,C a :=
    ((baseEmbed_mono_r427 Q (show t ≤ m0 from inf_le_left)).trans h0).trans_eq hCV.symm
  have hBound : baseEmbed Q t≤V b := by
    apply (le_inf le_rfl hAll).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro j
    by_cases hj : j≤b
    · exact inf_le_right.trans ((firstChoiceCell_le_r435 V j).trans
        (compl_le_compl (aboveValue_antitone_r431 g hj)))
    · have hJ : t≤(W j)ᶜ := inf_le_right.trans (compl_le_compl
        (le_iSup (fun k : {k : OmegaOneIndex // b < k} => W k.val) ⟨j,lt_of_not_ge hj⟩))
      have hT : baseEmbed Q t≤(baseEmbed Q (W j))ᶜ :=
        (baseEmbed_mono_r427 Q hJ).trans_eq (baseEmbed_compl_r427 Q _)
      have hC : C j≤baseEmbed Q (W j) := (supportProjection_le_iff_r428 Q _ _).mp le_rfl
      have hD : Disjoint (baseEmbed Q (W j))ᶜ (baseEmbed Q (W j)) := disjoint_compl_left
      exact ((inf_le_inf hT hC).trans (disjoint_iff_inf_le.mp hD)).trans bot_le
  obtain ⟨i,hi⟩ := OmegaOneIndex_countable_bounded_r61 {b} (Set.countable_singleton b)
  have hI : b< i := hi b (Set.mem_singleton _)
  have hGI : g i≤aboveValue g b := le_iSup (fun k : {k : OmegaOneIndex // b < k} => g k.val) ⟨i,hI⟩
  have hMeet : g i⊓baseEmbed Q t=⊥ :=
    le_bot_iff.mp ((inf_le_inf hGI hBound).trans (disjoint_iff_inf_le.mp disjoint_compl_right))
  have hP := supportProjection_meet_base_r428 Q (g i) t
  rw [hMeet,(supportProjection_zero_iff_r428 Q _).mpr rfl] at hP
  have hTM : t≤ m := inf_le_left.trans inf_le_left
  exact ht (le_bot_iff.mp ((le_inf (hTM.trans (hG i)) le_rfl).trans_eq hP.symm))

end RelativeOCA
end JSP000933
