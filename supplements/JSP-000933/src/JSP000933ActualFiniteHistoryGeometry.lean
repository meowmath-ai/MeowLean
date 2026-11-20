import JSP000933ActualStageHistoryReadback

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def GoodStageHistory {n : ℕ} (h : ActualStageHistory n) : Prop :=
  ∀ k<n, (historyStage h k).admissible k (stageLeftFromHistory h k) (stageOutFromHistory h k)

theorem ActualStageTower.good_history_r354 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (h : ActualStageHistory n)
    (hh : (T.level n).weight h≠⊥) : GoodStageHistory h :=
  fun k hk => T.stageOfHistory_admissible_r353 h hh k hk

theorem nat_initial_strict_ladder_r354 (N : ℕ) (f : ℕ → ℕ)
    (h : ∀ k, k+1<N → f k<f (k+1)) : ∀ i j, i<j → j<N → f i<f j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hij hJ
    by_cases hi : i=j
    · subst i
      exact h j hJ
    · exact (ih (by omega) (by omega)).trans (h j hJ)

theorem nat_initial_ge_index_r354 (N : ℕ) (f : ℕ → ℕ)
    (h : ∀ k, k+1<N → f k<f (k+1)) : ∀ j<N, j≤f j := by
  intro j
  induction j with
  | zero => intro _; exact Nat.zero_le _
  | succ j ih =>
    intro hj
    exact (Nat.succ_le_succ (ih (by omega))).trans (h j hj)

namespace GoodStageHistory

variable {n : ℕ} {H : ActualStageHistory n} (h : GoodStageHistory H)
include h

theorem left_link_r354 (k : ℕ) (hk : k+1<n) :
    (historyStage H (k+1)).left=(historyStage H k).nextLeft := by
  have he := (h (k+1) hk).1
  simpa [stageLeftFromHistory] using he

theorem out_step_r354 (k : ℕ) (hk : k+1<n) :
    (historyStage H k).out<(historyStage H (k+1)).out := by
  have he := (h (k+1) hk).2.2.1
  simpa [stageOutFromHistory] using he

theorem right_before_nextLeft_r354 (k : ℕ) (hk : k+1<n) :
    (historyStage H k).right<(historyStage H (k+1)).left := by
  rw [h.left_link_r354 k hk]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem left_step_r354 (k : ℕ) (hk : k+1<n) :
    (historyStage H k).left<(historyStage H (k+1)).left :=
  ((h k (by omega)).2.1).trans_lt (h.right_before_nextLeft_r354 k hk)

theorem left_increases_r354 {k j : ℕ} (hkj : k<j) (hj : j<n) :
    (historyStage H k).left<(historyStage H j).left :=
  nat_initial_strict_ladder_r354 n (fun i => (historyStage H i).left) h.left_step_r354 k j hkj hj

theorem out_increases_r354 {k j : ℕ} (hkj : k<j) (hj : j<n) :
    (historyStage H k).out<(historyStage H j).out :=
  nat_initial_strict_ladder_r354 n (fun i => (historyStage H i).out) h.out_step_r354 k j hkj hj

theorem left_ge_index_r354 (k : ℕ) (hk : k<n) : k≤(historyStage H k).left :=
  nat_initial_ge_index_r354 n (fun i => (historyStage H i).left) h.left_step_r354 k hk

theorem out_ge_index_r354 (k : ℕ) (hk : k<n) : k≤(historyStage H k).out :=
  nat_initial_ge_index_r354 n (fun i => (historyStage H i).out) h.out_step_r354 k hk

theorem source_before_nextLeft_r354 {k m : ℕ} (hk : k+1<n)
    (hm : m∈justSourceBlock (historyStage H k).position) :
    m<(historyStage H (k+1)).left := by
  rw [h.left_link_r354 k hk]
  exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)).trans_le (le_max_right _ _)

theorem source_before_laterLeft_r354 {k j m : ℕ} (hk : k<j) (hj : j<n)
    (hm : m∈justSourceBlock (historyStage H k).position) :
    m<(historyStage H j).left := by
  have hN := h.source_before_nextLeft_r354 ((Nat.succ_le_of_lt hk).trans_lt hj) hm
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with he | hlt
  · subst j
    exact hN
  · exact hN.trans (h.left_increases_r354 hlt hj)

theorem nextRight_le_laterRight_r354 {k j : ℕ} (hkj : k+1≤j) (hj : j<n) :
    (historyStage H (k+1)).right≤(historyStage H j).right := by
  rcases eq_or_lt_of_le hkj with he | hlt
  · rw [he]
  · exact (nat_initial_strict_ladder_r354 n (fun i => (historyStage H i).right)
      (fun i hi => (h.right_before_nextLeft_r354 i hi).trans_le (h (i+1) hi).2.1)
      (k+1) j hlt hj).le

theorem source_after_right_r354 {k m : ℕ} (hk : k<n)
    (hm : m∈justSourceBlock (historyStage H k).position) :
    (historyStage H k).right≤ m := (h k hk).2.2.2.2 m hm

theorem source_ge_index_r354 {k m : ℕ} (hk : k<n)
    (hm : m∈justSourceBlock (historyStage H k).position) : k≤ m :=
  (h.left_ge_index_r354 k hk).trans ((h k hk).2.1.trans (h.source_after_right_r354 hk hm))

theorem middle_disjoint_source_r354 {k j m : ℕ} (hk : k<n) (hj : j<n)
    (hl : (historyStage H k).left≤ m) (hr : m<(historyStage H k).right)
    (hm : m∈justSourceBlock (historyStage H j).position) : False := by
  rcases lt_trichotomy j k with hJ | rfl | hJ
  · exact (not_lt_of_ge hl) (h.source_before_laterLeft_r354 hJ hk hm)
  · exact (not_lt_of_ge (h.source_after_right_r354 hj hm)) hr
  · have hK : k+1<n := (Nat.succ_le_of_lt hJ).trans_lt hj
    have hR : m<(historyStage H (k+1)).right :=
      (hr.trans (h.right_before_nextLeft_r354 k hK)).trans_le (h (k+1) hK).2.1
    exact (not_lt_of_ge ((h.nextRight_le_laterRight_r354 (Nat.succ_le_of_lt hJ) hj).trans
      (h.source_after_right_r354 hj hm))) hR

end GoodStageHistory

end SetLanguage
end JSP000933
