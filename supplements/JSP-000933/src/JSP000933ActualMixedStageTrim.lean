import JSP000933ActualRawWindowError

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualAfterStageOut {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (J m : ℕ) : B :=
  actualHistoryRead T (J+1) (fun H => crispTruth B ((historyStage H J).out≤ m))

theorem actualAfterStageOut_mask_r361 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N)
    (J m : ℕ) (hJ : J<N) :
    (T.level N).weight H⊓actualAfterStageOut T J m=
      (T.level N).weight H⊓crispTruth B ((historyStage H J).out≤ m) := by
  unfold actualAfterStageOut
  apply actualHistoryRead_mask_r355 T (Nat.succ_le_of_lt hJ)
  intro A hA
  rw [← hA J (Nat.lt_succ_self J)]

theorem actualTrim_output_harmEq_r361 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (J : ℕ) (a : ℕ → B) :
    LocalEq true p (bitsMeet (actualAfterStageOut T J) a) a := by
  let u := bitsMeet (actualAfterStageOut T J) a
  suffices H : p≤liveLE true u a⊓liveLE true a u by
    exact ⟨H.trans inf_le_left,H.trans inf_le_right⟩
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨A,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (T.level (J+1)).weight
    (hqp.trans_eq (T.level (J+1)).covers.symm)
  have hEq := harmonicLocalEq_late_agreement_r341 (p := r) u a (historyStage A J).out (fun m hm => by
    have he := mask_under_r302 hR (actualAfterStageOut_mask_r361 T A J m (Nat.lt_succ_self J))
    have e : r⊓actualAfterStageOut T J m=r⊓(⊤ : B) := by
      simpa only [crispTruth,ite_eq_left hm] using he
    exact (mask_inf_congr_r126 e (show r⊓a m=r⊓a m from rfl)).trans (by rw [top_inf_eq]))
  exact ⟨r,hr,hrq,le_inf hEq.1 hEq.2⟩

theorem actualTrim_window_mask_r361 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N)
    (hq : q≤(T.level N).weight H) (hH : (T.level N).weight H≠⊥)
    (J k m : ℕ) (hJk : J≤k) (hk : k+1<N) (a : ℕ → B) :
    q⊓bitsMeet (crispStageWindow H k) (bitsMeet (actualAfterStageOut T J) a) m=
      q⊓bitsMeet (crispStageWindow H k) a m := by
  by_cases hm : m∈groundStageWindow H k
  · have hOut : (historyStage H J).out≤ m := by
      rcases eq_or_lt_of_le hJk with he | hlt
      · simpa only [he] using (Finset.mem_Ico.mp hm).1
      · exact ((T.good_history_r354 H hH).out_increases_r354 hlt (by omega)).le.trans
          (Finset.mem_Ico.mp hm).1
    have he := mask_under_r302 hq (actualAfterStageOut_mask_r361 T H J m (by omega))
    have e : q⊓actualAfterStageOut T J m=q⊓(⊤ : B) := by
      simpa only [crispTruth,ite_eq_left hOut] using he
    have hA := mask_inf_congr_r126 e (show q⊓a m=q⊓a m from rfl)
    exact mask_inf_congr_r126 rfl (hA.trans (by rw [top_inf_eq]))
  · simp [bitsMeet,crispStageWindow,crispTruth,hm]

end SetLanguage
end JSP000933
