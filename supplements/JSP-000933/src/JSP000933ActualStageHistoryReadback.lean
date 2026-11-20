import JSP000933ActualStageHistoryTower

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def historyStage : {n : ℕ} → ActualStageHistory n → ℕ → ActualGroundStage
  | 0, _, _ => ⟨0,0,0,0,[]⟩
  | n+1, h, k => if k=n then h.2 else historyStage h.1 k

@[simp] theorem historyStage_last_r353 {n : ℕ} (h : ActualStageHistory (n+1)) :
    historyStage h n=h.2 := by simp [historyStage]

theorem historyStage_before_r353 {n : ℕ} (h : ActualStageHistory (n+1)) {k : ℕ} (hk : k<n) :
    historyStage h k=historyStage h.1 k := by simp [historyStage,Nat.ne_of_lt hk]

def stageLeftFromHistory {n : ℕ} (h : ActualStageHistory n) (k : ℕ) : ℕ :=
  if k=0 then 0 else (historyStage h (k-1)).nextLeft

def stageOutFromHistory {n : ℕ} (h : ActualStageHistory n) (k : ℕ) : ℕ :=
  if k=0 then 0 else (historyStage h (k-1)).out+1

theorem stageLeftFromHistory_last_r353 {n : ℕ} (h : ActualStageHistory (n+1)) :
    stageLeftFromHistory h n=historyNextLeft h.1 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp [stageLeftFromHistory,historyNextLeft,
      historyStage_before_r353 h (Nat.lt_succ_self n),historyStage_last_r353]

theorem stageOutFromHistory_last_r353 {n : ℕ} (h : ActualStageHistory (n+1)) :
    stageOutFromHistory h n=historyNextOut h.1 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp [stageOutFromHistory,historyNextOut,
      historyStage_before_r353 h (Nat.lt_succ_self n),historyStage_last_r353]

theorem ActualStageTower.exists_prefix_support_r353 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (h : n≤N) (H : ActualStageHistory N) :
    ∃ A : ActualStageHistory n, (T.level N).weight H≤(T.level n).weight A ∧
      ∀ k<n, historyStage H k=historyStage A k := by
  induction N with
  | zero =>
    have hn : n=0 := Nat.eq_zero_of_le_zero h
    subst n
    exact ⟨H,le_rfl,fun _ _ => rfl⟩
  | succ N ih =>
    by_cases hn : n=N+1
    · subst n
      exact ⟨H,le_rfl,fun _ _ => rfl⟩
    · have hN : n≤N := by omega
      obtain ⟨A,hA,hE⟩ := ih hN H.1
      exact ⟨A,(T.refines N H).trans hA,fun k hk =>
        (historyStage_before_r353 H (hk.trans_le hN)).trans (hE k hk)⟩

theorem ActualStageTower.stageOfHistoryValue_r353 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (h : ActualStageHistory n) (k : ℕ) (hk : k<n) :
    (T.level n).weight h≤actualStageValue c L k (stageLeftFromHistory h k) (stageOutFromHistory h k)
      (historyStage h k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [historyStage_last_r353,stageLeftFromHistory_last_r353,stageOutFromHistory_last_r353]
      exact (T.valid (n+1) h).trans inf_le_right
    · have hK : k<n := by omega
      have hSt (j : ℕ) (hj : j≤k) : historyStage h j=historyStage h.1 j :=
        historyStage_before_r353 h (hj.trans_lt hK)
      rw [show stageLeftFromHistory h k=stageLeftFromHistory h.1 k by
            unfold stageLeftFromHistory
            rw [hSt (k-1) (Nat.sub_le _ _)],
          show stageOutFromHistory h k=stageOutFromHistory h.1 k by
            unfold stageOutFromHistory
            rw [hSt (k-1) (Nat.sub_le _ _)],
          hSt k le_rfl]
      exact (T.refines n h).trans (ih h.1 hK)

theorem ActualStageTower.stageOfHistory_admissible_r353 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (h : ActualStageHistory n)
    (hn : (T.level n).weight h≠⊥) (k : ℕ) (hk : k<n) :
    (historyStage h k).admissible k (stageLeftFromHistory h k) (stageOutFromHistory h k) :=
  prop_of_le_crisp_nonzero_r190 hn ((T.stageOfHistoryValue_r353 h k hk).trans inf_le_left)

end SetLanguage
end JSP000933
