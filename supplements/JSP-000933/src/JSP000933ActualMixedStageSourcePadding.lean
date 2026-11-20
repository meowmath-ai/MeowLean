import JSP000933ActualFiniteHistoryGeometry

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem indexedPartition_mask_value_r355 {α : Type} {p : B} (P : IndexedPartition B α p)
    (a : α) (F : α → B) : P.weight a⊓(⨆ b, P.weight b⊓F b)=P.weight a⊓F a := by
  apply le_antisymm
  · rw [inf_iSup_eq]
    apply iSup_le
    intro b
    by_cases he : a=b
    · subst b
      simp only [← inf_assoc,inf_idem,le_rfl]
    · rw [← inf_assoc,(P.separate a b he).eq_bot,bot_inf_eq]
      exact bot_le
  · exact le_inf inf_le_left (le_iSup_of_le a le_rfl)

noncomputable def actualHistoryRead {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (N : ℕ) (F : ActualStageHistory N → B) : B :=
  ⨆ h, (T.level N).weight h⊓F h

theorem actualHistoryRead_mask_r355 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (hn : n≤N) (H : ActualStageHistory N)
    (F : ActualStageHistory n → B) (W : B)
    (hF : ∀ A : ActualStageHistory n, (∀ k<n, historyStage H k=historyStage A k) → F A=W) :
    (T.level N).weight H⊓actualHistoryRead T n F=(T.level N).weight H⊓W := by
  obtain ⟨A,hBelow,hEq⟩ := T.exists_prefix_support_r353 hn H
  have he := indexedPartition_mask_value_r355 (T.level n) A F
  rw [hF A hEq] at he
  exact mask_under_r302 hBelow he

def historySourceDigit {N : ℕ} (H : ActualStageHistory N) (m : ℕ) : Prop :=
  ∃ k≤ m, m∈justSourceBlock (historyStage H k).position

def historyPaddingDigit {N : ℕ} (H : ActualStageHistory N) (m : ℕ) : Prop :=
  ∃ k≤ m, (historyStage H k).left≤ m ∧ m<(historyStage H k).right ∧ wordBit (historyStage H k).pad m=true

noncomputable def actualSourceUnion {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (m : ℕ) : B :=
  actualHistoryRead T (m+1) (fun H => crispTruth B (historySourceDigit H m))

noncomputable def actualPaddingUnion {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (m : ℕ) : B :=
  actualHistoryRead T (m+1) (fun H => crispTruth B (historyPaddingDigit H m))

theorem actualSourceUnion_mask_r355 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N) (m : ℕ) (hm : m<N) :
    (T.level N).weight H⊓actualSourceUnion T m=
      (T.level N).weight H⊓crispTruth B (historySourceDigit H m) := by
  unfold actualSourceUnion
  apply actualHistoryRead_mask_r355 T (Nat.succ_le_of_lt hm)
  intro A hA
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨k,hK,hM⟩
    exact ⟨k,hK,by simpa only [hA k (Nat.lt_succ_of_le hK)] using hM⟩
  · rintro ⟨k,hK,hM⟩
    exact ⟨k,hK,by simpa only [← hA k (Nat.lt_succ_of_le hK)] using hM⟩

theorem actualPaddingUnion_mask_r355 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N) (m : ℕ) (hm : m<N) :
    (T.level N).weight H⊓actualPaddingUnion T m=
      (T.level N).weight H⊓crispTruth B (historyPaddingDigit H m) := by
  unfold actualPaddingUnion
  apply actualHistoryRead_mask_r355 T (Nat.succ_le_of_lt hm)
  intro A hA
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨k,hK,hM⟩
    exact ⟨k,hK,by simpa only [hA k (Nat.lt_succ_of_le hK)] using hM⟩
  · rintro ⟨k,hK,hM⟩
    exact ⟨k,hK,by simpa only [← hA k (Nat.lt_succ_of_le hK)] using hM⟩

end SetLanguage
end JSP000933
