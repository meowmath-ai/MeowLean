import JSP000933ActualMixedStageSourcePadding

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem GoodStageHistory.right_before_laterLeft_r356 {n : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) {j k : ℕ} (hk : j<k) (hn : k<n) :
    (historyStage H j).right<(historyStage H k).left := by
  have hRight := h.right_before_nextLeft_r354 j ((Nat.succ_le_of_lt hk).trans_lt hn)
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with he | hlt
  · subst k
    exact hRight
  · exact hRight.trans (h.left_increases_r354 hlt hn)

theorem GoodStageHistory.padding_middle_iff_r356 {n : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) (k m : ℕ) (hk : k<n) (hm : m<n)
    (hl : (historyStage H k).left≤ m) (hr : m<(historyStage H k).right) :
    historyPaddingDigit H m ↔ wordBit (historyStage H k).pad m=true := by
  constructor
  · rintro ⟨j,hJ,hJL,hJR,hE⟩
    have hj : j<n := hJ.trans_lt hm
    rcases lt_trichotomy j k with hJK | rfl | hKJ
    · exact False.elim ((not_lt_of_ge hl) (hJR.trans (h.right_before_laterLeft_r356 hJK hk)))
    · exact hE
    · exact False.elim ((not_lt_of_ge hJL) (hr.trans (h.right_before_laterLeft_r356 hKJ hj)))
  · intro he
    exact ⟨k,(h.left_ge_index_r354 k hk).trans hl,hl,hr,he⟩

theorem GoodStageHistory.source_middle_iff_r356 {n : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) (k m : ℕ) (hk : k+1<n) (hm : m<n)
    (hl : (historyStage H k).left≤ m) (hr : m<(historyStage H (k+1)).right) :
    historySourceDigit H m ↔ m∈justSourceBlock (historyStage H k).position := by
  have hK : k<n := by omega
  constructor
  · rintro ⟨j,hJ,hM⟩
    have hj : j<n := hJ.trans_lt hm
    rcases lt_trichotomy j k with hJK | rfl | hKJ
    · exact False.elim ((not_lt_of_ge hl) (h.source_before_laterLeft_r354 hJK hK hM))
    · exact hM
    · exact False.elim ((not_lt_of_ge ((h.nextRight_le_laterRight_r354 (Nat.succ_le_of_lt hKJ) hj).trans
      (h.source_after_right_r354 hj hM))) hr)
  · intro hM
    exact ⟨k,h.source_ge_index_r354 hK hM,hM⟩

theorem crisp_wordBit_r356 (w : Word) (m : ℕ) :
    crispTruth B (wordBit w m=true)=paddedWordBits w m := by
  unfold paddedWordBits
  cases wordBit w m <;> simp [crispTruth,truthBit]

theorem actualPaddingUnion_middle_mask_r356 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n)
    (hq : (T.level n).weight H≠⊥) (k m : ℕ) (hk : k<n) (hm : m<n)
    (hl : (historyStage H k).left≤ m) (hr : m<(historyStage H k).right) :
    (T.level n).weight H⊓actualPaddingUnion T m=
      (T.level n).weight H⊓paddedWordBits (historyStage H k).pad m := by
  rw [actualPaddingUnion_mask_r355 T H m hm,
    crispTruth_propext_r188 ((T.good_history_r354 H hq).padding_middle_iff_r356 k m hk hm hl hr),crisp_wordBit_r356]

theorem actualPadding_disjoint_source_r356 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (m : ℕ) :
    p⊓(actualPaddingUnion T m⊓actualSourceUnion T m)=⊥ := by
  apply le_bot_iff.mp
  apply le_of_dense_named_refinements_r219
  intro q hq hpq
  obtain ⟨H,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (T.level (m+1)).weight
    ((hpq.trans inf_le_left).trans_eq (T.level (m+1)).covers.symm)
  have hW : (T.level (m+1)).weight H≠⊥ := fun he => hr (le_bot_iff.mp (hR.trans_eq he))
  have hg := T.good_history_r354 H hW
  have hN : ¬(historyPaddingDigit H m ∧ historySourceDigit H m) := by
    rintro ⟨⟨i,hi,hL,hU,_⟩,⟨j,hj,hJ⟩⟩
    exact hg.middle_disjoint_source_r354 (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hL hU hJ
  have he := mask_inf_congr_r126
    (mask_under_r302 hR (actualPaddingUnion_mask_r355 T H m (Nat.lt_succ_self m)))
    (mask_under_r302 hR (actualSourceUnion_mask_r355 T H m (Nat.lt_succ_self m)))
  have h0 : r⊓(actualPaddingUnion T m⊓actualSourceUnion T m)=⊥ := by
    rw [he,← crisp_and_r190,crispTruth,ite_eq_right hN,inf_bot_eq]
  have hr0 : r≤⊥ := ((le_inf le_rfl (hrq.trans (hpq.trans inf_le_right))).trans_eq h0)
  exact False.elim (hr (le_bot_iff.mp hr0))

theorem actualSourceUnion_below_cap_r356 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : p≤bitsBelowValue (actualSourceUnion T) c := by
  unfold bitsBelowValue
  apply le_iInf
  intro m
  apply (le_materialImp_iff_r126 _ _ _).mpr
  apply le_of_dense_named_refinements_r219
  intro q hq hpq
  obtain ⟨H,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (T.level (m+1)).weight
    ((hpq.trans inf_le_left).trans_eq (T.level (m+1)).covers.symm)
  have he := mask_under_r302 hR (actualSourceUnion_mask_r355 T H m (Nat.lt_succ_self m))
  have hT : r≤crispTruth B (historySourceDigit H m) :=
    ((le_inf le_rfl (hrq.trans (hpq.trans inf_le_right))).trans_eq he).trans inf_le_right
  obtain ⟨k,hk,hm⟩ := prop_of_le_crisp_nonzero_r190 hr hT
  have hStage := T.stageOfHistoryValue_r353 H k (Nat.lt_succ_of_le hk)
  have hWhole : r≤actualIncludesBlock c (historyStage H k).position :=
    hR.trans (hStage.trans (inf_le_right.trans inf_le_left))
  exact ⟨r,hr,hrq,hWhole.trans (iInf_le (fun j : ↥(justSourceBlock (historyStage H k).position) => c j.val) ⟨m,hm⟩)⟩

end SetLanguage
end JSP000933
