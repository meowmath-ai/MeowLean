import JSP000933ActualOverlappingStageSnapshots

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def crispStageSource {n : ℕ} (H : ActualStageHistory n) (k m : ℕ) : B :=
  crispTruth B (m∈justSourceBlock (historyStage H k).position)

noncomputable def actualPaddedInput {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) : ℕ → B :=
  bitsJoin (actualPaddingUnion T) x

noncomputable def actualLocalRawInput {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n) (k : ℕ) (x : ℕ → B) : ℕ → B :=
  actualPaddedInput T (bitsMeet (crispStageSource H k) x)

noncomputable def actualRawOutputAt {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n) (x : ℕ → B) (m : ℕ) : B :=
  ⨆ k : Fin (m+1), crispTruth B (m∈groundStageWindow H k.val)⊓L (actualLocalRawInput T H k.val x) m

noncomputable def actualRawOutput {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) (m : ℕ) : B :=
  actualHistoryRead T (m+2) (fun H => actualRawOutputAt T H x m)

theorem actualRawOutput_snapshot_r358 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n) (x : ℕ → B) (m : ℕ) (hm : m+2≤n) :
    (T.level n).weight H⊓actualRawOutput T x m=(T.level n).weight H⊓actualRawOutputAt T H x m := by
  unfold actualRawOutput
  apply actualHistoryRead_mask_r355 T hm
  intro A hA
  unfold actualRawOutputAt
  apply congrArg iSup
  funext k
  have he := hA k.val (by have hh := k.isLt; omega)
  have he' := hA (k.val+1) (by have hh := k.isLt; omega)
  have hs : (crispStageSource A k.val : ℕ → B) = crispStageSource H k.val := by
    funext i
    unfold crispStageSource
    rw [he]
  simp only [groundStageWindow,actualLocalRawInput,← he,← he']
  rw [hs]

theorem actualRawOutput_window_mask_r358 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n)
    (hH : (T.level n).weight H≠⊥) (x : ℕ → B) (k m : ℕ) (hm : m+2≤n) (hk : k+1<n)
    (hM : m∈groundStageWindow H k) :
    (T.level n).weight H⊓actualRawOutput T x m=(T.level n).weight H⊓L (actualLocalRawInput T H k x) m := by
  have hg := T.good_history_r354 H hH
  have hK : k≤ m := (hg.out_ge_index_r354 k (by omega)).trans (Finset.mem_Ico.mp hM).1
  rw [actualRawOutput_snapshot_r358 T H x m hm]
  unfold actualRawOutputAt
  suffices hEq : (⨆ j : Fin (m+1), crispTruth B (m∈groundStageWindow H j.val)⊓L (actualLocalRawInput T H j.val x) m)=
      L (actualLocalRawInput T H k x) m by rw [hEq]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hJ : m∈groundStageWindow H j.val
    · have he : j.val=k := hg.window_unique_r357 (by have hh := j.isLt; omega) hk hJ hM
      simp only [he,crispTruth,ite_eq_left hM,top_inf_eq,le_rfl]
    · simp only [crispTruth,ite_eq_right hJ,bot_inf_eq,bot_le]
  · apply le_iSup_of_le (⟨k,Nat.lt_succ_of_le hK⟩ : Fin (m+1))
    simp only [crispTruth,ite_eq_left hM,top_inf_eq,le_rfl]

theorem actualRawOutput_before_first_mask_r358 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (H : ActualStageHistory n)
    (hH : (T.level n).weight H≠⊥) (x : ℕ → B) (m : ℕ) (hm : m+2≤n)
    (h0 : m<(historyStage H 0).out) :
    (T.level n).weight H⊓actualRawOutput T x m=⊥ := by
  rw [actualRawOutput_snapshot_r358 T H x m hm]
  have hg := T.good_history_r354 H hH
  have hEq : actualRawOutputAt T H x m=⊥ := by
    apply le_bot_iff.mp
    unfold actualRawOutputAt
    apply iSup_le
    intro k
    have hK : (historyStage H 0).out≤(historyStage H k.val).out := by
      by_cases he : k.val=0
      · rw [he]
      · exact (hg.out_increases_r354 (Nat.pos_of_ne_zero he) (by have hh := k.isLt; omega)).le
    have hN : m∉groundStageWindow H k.val := fun hh => not_lt_of_ge
      (hK.trans (Finset.mem_Ico.mp hh).1) h0
    simp only [crispTruth,ite_eq_right hN,bot_inf_eq,le_rfl]
  rw [hEq,inf_bot_eq]

end SetLanguage
end JSP000933
