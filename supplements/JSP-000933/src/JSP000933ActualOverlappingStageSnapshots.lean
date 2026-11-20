import JSP000933ActualStageDisjointPadding

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem ActualStageTower.snapshots_agree_r357 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (hN : n≤N)
    (A : ActualStageHistory n) (H : ActualStageHistory N) {q : B} (hq : q≠⊥)
    (hA : q≤(T.level n).weight A) (hH : q≤(T.level N).weight H) :
    ∀ k<n, historyStage H k=historyStage A k := by
  obtain ⟨A',hSupp,hE⟩ := T.exists_prefix_support_r353 hN H
  by_cases he : A'=A
  · subst A'
    exact hE
  · exact False.elim (hq (((T.level n).separate A' A he).out q (hH.trans hSupp) hA))

theorem ActualStageTower.exists_larger_snapshot_r357 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (hN : n≤N)
    (A : ActualStageHistory n) {q : B} (hq : q≠⊥)
    (hA : q≤(T.level n).weight A) :
    ∃ (H : ActualStageHistory N) (r : B), r≠⊥ ∧ r≤q ∧ r≤(T.level N).weight H ∧
      ∀ k<n, historyStage H k=historyStage A k := by
  have hp : q≤p := hA.trans ((T.level n).weight_le_r215 A)
  obtain ⟨H,r,hr,hrq,hH⟩ := exists_nonzero_below_choice_r135 q hq (T.level N).weight
    (hp.trans_eq (T.level N).covers.symm)
  exact ⟨H,r,hr,hrq,hH,T.snapshots_agree_r357 hN A H hr (hrq.trans hA) hH⟩

def groundStageWindow {n : ℕ} (H : ActualStageHistory n) (k : ℕ) : Finset ℕ :=
  Finset.Ico (historyStage H k).out (historyStage H (k+1)).out

theorem GoodStageHistory.window_unique_r357 {n m k j : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) (hk : k+1<n) (hj : j+1<n)
    (hMK : m∈groundStageWindow H k) (hMJ : m∈groundStageWindow H j) : k=j := by
  obtain ⟨hK,hK'⟩ := Finset.mem_Ico.mp hMK
  obtain ⟨hJ,hJ'⟩ := Finset.mem_Ico.mp hMJ
  rcases lt_trichotomy k j with hlt | he | hgt
  · have hN : (historyStage H (k+1)).out≤(historyStage H j).out := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hEq | hLt
      · exact (congrArg (fun i => (historyStage H i).out) hEq).le
      · exact (h.out_increases_r354 hLt (by omega)).le
    exact False.elim (not_lt_of_ge (hN.trans hJ) hK')
  · exact he
  · have hN : (historyStage H (j+1)).out≤(historyStage H k).out := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hEq | hLt
      · exact (congrArg (fun i => (historyStage H i).out) hEq).le
      · exact (h.out_increases_r354 hLt (by omega)).le
    exact False.elim (not_lt_of_ge (hN.trans hK) hJ')

theorem GoodStageHistory.window_exists_to_r357 {n m : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) (h0 : (historyStage H 0).out≤ m) :
    ∀ j<n, m<(historyStage H j).out → ∃ k<j, m∈groundStageWindow H k := by
  intro j
  induction j with
  | zero => intro _ hJ; exact False.elim (not_lt_of_ge h0 hJ)
  | succ j ih =>
    intro hj hJ
    by_cases hL : m<(historyStage H j).out
    · obtain ⟨k,hk,hM⟩ := ih (by omega) hL
      exact ⟨k,hk.trans (Nat.lt_succ_self j),hM⟩
    · exact ⟨j,Nat.lt_succ_self j,Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hL,hJ⟩⟩

theorem GoodStageHistory.window_exists_r357 {n m : ℕ} {H : ActualStageHistory n}
    (h : GoodStageHistory H) (hn : m+2≤n) (h0 : (historyStage H 0).out≤ m) :
    ∃ k≤ m, m∈groundStageWindow H k := by
  have hJ : m+1<n := by omega
  have hUpper : m<(historyStage H (m+1)).out :=
    (Nat.lt_succ_self m).trans_le (h.out_ge_index_r354 (m+1) hJ)
  obtain ⟨k,hk,hK⟩ := h.window_exists_to_r357 h0 (m+1) hJ hUpper
  exact ⟨k,Nat.le_of_lt_succ hk,hK⟩

end SetLanguage
end JSP000933
