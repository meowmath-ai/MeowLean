import JSP000933ActualRawLocalOutput

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualSource_middle_mask_r359 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : ActualStageHistory n)
    (hq : q≤(T.level n).weight A) (k m : ℕ) (hk : k+1<n)
    (hl : (historyStage A k).left≤ m) (hr : m<(historyStage A (k+1)).right) :
    q⊓actualSourceUnion T m=q⊓crispStageSource A k m := by
  apply (le_bitEq_iff_r126 _ _ _).mp
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  let N := max n (m+1)
  obtain ⟨H,r,hR,hrs,hrH,hE⟩ := T.exists_larger_snapshot_r357 (le_max_left n (m+1)) A hs (hsq.trans hq)
  have hValid : (T.level N).weight H≠⊥ := fun he => hR (le_bot_iff.mp (hrH.trans_eq he))
  have hNg : n≤N := le_max_left _ _
  have hm : m<N := (Nat.lt_succ_self m).trans_le (le_max_right n (m+1))
  have hk0 : k<n := by omega
  have hEK := hE k hk0
  have hE1 := hE (k+1) hk
  have hLeft : (historyStage H k).left≤ m := by simpa only [hEK] using hl
  have hRight : m<(historyStage H (k+1)).right := by simpa only [hE1] using hr
  have hG := (T.good_history_r354 H hValid).source_middle_iff_r356 k m (hk.trans_le hNg) hm hLeft hRight
  have he := actualSourceUnion_mask_r355 T H m hm
  rw [crispTruth_propext_r188 hG,hEK] at he
  exact ⟨r,hR,hrs,(le_bitEq_iff_r126 _ _ _).mpr (mask_under_r302 hrH he)⟩

theorem actualPadding_middle_mask_r359 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : ActualStageHistory n)
    (hq : q≤(T.level n).weight A) (k m : ℕ) (hk : k<n)
    (hl : (historyStage A k).left≤ m) (hr : m<(historyStage A k).right) :
    q⊓actualPaddingUnion T m=q⊓paddedWordBits (historyStage A k).pad m := by
  apply (le_bitEq_iff_r126 _ _ _).mp
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  let N := max n (m+1)
  obtain ⟨H,r,hR,hrs,hrH,hE⟩ := T.exists_larger_snapshot_r357 (le_max_left n (m+1)) A hs (hsq.trans hq)
  have hValid : (T.level N).weight H≠⊥ := fun he => hR (le_bot_iff.mp (hrH.trans_eq he))
  have hm : m<N := (Nat.lt_succ_self m).trans_le (le_max_right n (m+1))
  have hEK := hE k hk
  have hLeft : (historyStage H k).left≤ m := by simpa only [hEK] using hl
  have hRight : m<(historyStage H k).right := by simpa only [hEK] using hr
  have he := actualPaddingUnion_middle_mask_r356 T H hValid k m (hk.trans_le (le_max_left _ _)) hm hLeft hRight
  rw [hEK] at he
  exact ⟨r,hR,hrs,(le_bitEq_iff_r126 _ _ _).mpr (mask_under_r302 hrH he)⟩

theorem actualPaddedInput_middle_mask_r359 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : ActualStageHistory n)
    (hA : (T.level n).weight A≠⊥) (hq : q≤(T.level n).weight A) (x : ℕ → B)
    (hX : q≤bitsBelowValue x (actualSourceUnion T)) (k m : ℕ) (hk : k+1<n)
    (hl : (historyStage A k).left≤ m) (hr : m<(historyStage A k).right) :
    q⊓actualPaddedInput T x m=q⊓paddedWordBits (historyStage A k).pad m := by
  have hg := T.good_history_r354 A hA
  have hRight : m<(historyStage A (k+1)).right := (hr.trans
    (hg.right_before_nextLeft_r354 k hk)).trans_le (hg (k+1) hk).2.1
  have hZero : ¬m∈justSourceBlock (historyStage A k).position :=
    fun h => not_lt_of_ge (hg.source_after_right_r354 (by omega) h) hr
  have h0 : q⊓actualSourceUnion T m=⊥ := by
    rw [actualSource_middle_mask_r359 T A hq k m hk hl hRight,crispStageSource,crispTruth,ite_eq_right hZero,inf_bot_eq]
  have hX0 : q⊓x m=⊥ := le_bot_iff.mp ((le_inf inf_le_left (bitsBelowValue_apply_r256 hX m)).trans_eq h0)
  have hp := actualPadding_middle_mask_r359 T A hq k m (by omega) hl hr
  unfold actualPaddedInput bitsJoin
  rw [inf_sup_left,hp,hX0,sup_bot_eq]

theorem actualGraftInput_agrees_prefix_r359 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : ActualStageHistory n)
    (hq : q≤(T.level n).weight A) (x : ℕ → B) (hX : q≤bitsBelowValue x (actualSourceUnion T))
    (k : ℕ) (hk : k+1<n) :
    q≤actualPrefixMatch
      (actualPrefixPatch (historyStage A k).left (actualLocalRawInput T A k x) (actualPaddedInput T x))
      (actualLocalRawInput T A k x) (historyStage A (k+1)).right := by
  apply (le_actualPrefixMatch_iff_r351 _ _ _ _).mpr
  intro m hm
  by_cases hM : m<(historyStage A k).left
  · simp only [actualPrefixPatch,ite_eq_left hM]
  · rw [actualPrefixPatch,ite_eq_right hM]
    have hs := actualSource_middle_mask_r359 T A hq k m hk (Nat.le_of_not_gt hM) hm
    have he : q⊓(crispStageSource A k m⊓x m)=q⊓x m := by
      have hE := mask_inf_congr_r126 hs.symm (show q⊓x m=q⊓x m from rfl)
      refine hE.trans ?_
      calc
        q⊓(actualSourceUnion T m⊓x m)=(q⊓x m)⊓actualSourceUnion T m := by ac_rfl
        _=q⊓x m := inf_eq_left.mpr (bitsBelowValue_apply_r256 hX m)
    change q⊓(actualPaddingUnion T m⊔x m)=q⊓(actualPaddingUnion T m⊔(crispStageSource A k m⊓x m))
    exact mask_sup_congr_r211 rfl he.symm

end SetLanguage
end JSP000933
