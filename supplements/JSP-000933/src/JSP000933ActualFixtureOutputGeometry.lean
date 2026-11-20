import JSP000933ActualCollapseKernels

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem fixture_mainHistory_mask_r381 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : BlockFixture (n+1))
    (hA : q≤fixtureWeight T (n+1) A) :
    q≤(T.level (n+2)).weight A.2.history := actualBlockSnapshotValue_history_r367
  (show q≤actualBlockSnapshotValue T n A.2 from hA.trans inf_le_right)

theorem fixture_snapshotGeometry_r381 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : BlockFixture (n+1))
    (hq : q≠⊥) (hA : q≤fixtureWeight T (n+1) A) (i : Fin (n+1)) :
    ∀ k< i.val+2, historyStage A.2.history k=historyStage (fixtureSnapshot A i).history k := by
  have hI : i.val+2≤n+2 := by have hh := i.isLt; omega
  exact T.snapshots_agree_r357 hI (fixtureSnapshot A i).history A.2.history hq
    (actualBlockSnapshotValue_history_r367 (hA.trans (fixtureWeight_snapshot_r376 T A i)))
    (fixture_mainHistory_mask_r381 T A hA)

theorem fixture_output_at_window_or_zero_r381 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : BlockFixture (n+1))
    (hq : q≠⊥) (hA : q≤fixtureWeight T (n+1) A) (m : ℕ) (hm : m≤n) :
    (∃ i : Fin (n+1), m∈groundStageWindow (fixtureSnapshot A i).history i.val) ∨
      q⊓actualBlockClamp T m=⊥ := by
  let H := A.2.history
  have hH := fixture_mainHistory_mask_r381 T A hA
  have hV : (T.level (n+2)).weight H≠⊥ := fun he => hq (le_bot_iff.mp (hH.trans_eq he))
  let G := T.good_history_r354 H hV
  by_cases hFirst : (historyStage H 0).out≤ m
  · left
    obtain ⟨k,hk,hW⟩ := G.window_exists_r357 (by omega) hFirst
    let i : Fin (n+1) := ⟨k,Nat.lt_succ_of_le (hk.trans hm)⟩
    have he := fixture_snapshotGeometry_r381 T A hq hA i
    refine ⟨i,?_⟩
    unfold groundStageWindow at hW ⊢
    rw [← he i.val (by omega), ← he (i.val+1) (by omega)]
    exact hW
  · right
    have hRaw := actualRawOutput_before_first_mask_r358 T H hV (actualSourceUnion T) m
      (by omega) (Nat.lt_of_not_ge hFirst)
    have h0 : q ⊓ actualRawOutput T (actualSourceUnion T) m = ⊥ :=
      le_antisymm ((inf_le_inf_right _ hH).trans_eq hRaw) bot_le
    change q⊓(actualRawOutput T (actualSourceUnion T) m⊓L (actualSourceUnion T) m)=⊥
    rw [← inf_assoc,h0,bot_inf_eq]

theorem exists_actualGradeAtLeast_refinement_r381 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hq : q≠⊥) (hqp : q≤p) (hB : q≤(actualNoCollapseValue T)ᶜ) :
    ∀ J : ℕ, ∃ (n : ℕ) (A : BlockFixture n) (r : B),
      r≠⊥ ∧ r≤q ∧ r≤fixtureWeight T n A ∧ J≤fixtureGradeAt A n := by
  intro J
  induction J with
  | zero =>
    exact ⟨0,PUnit.unit,q,hq,le_rfl,hqp,Nat.zero_le _⟩
  | succ J ih =>
    obtain ⟨n,A,s,hs,hsq,hSA,hJ⟩ := ih
    obtain ⟨N,D,i,r,hr,hrs,hRD,hNI,hHit⟩ := exists_actualLateHit_refinement_r378 T hs
      (hsq.trans hqp) (hsq.trans hB) n
    have hn : n≤N := hNI.trans i.isLt.le
    have hE := fixtureSnapshots_agree_r378 T hn A D hr (hrs.trans hSA) hRD
    have hh : fixtureGradeAt D n=fixtureGradeAt A n := fixtureGrade_prefix_congr_r377 hn D A hE n le_rfl
    have hStep : J+1≤fixtureGradeAt D (i.val+1) := by
      rw [fixtureGrade_hit_r377 D i hHit]
      exact Nat.succ_le_succ ((hJ.trans_eq hh.symm).trans (fixtureGrade_mono_r377 D hNI))
    exact ⟨N,D,r,hr,hrs.trans hsq,hRD,hStep.trans (fixtureGrade_mono_r377 D (Nat.succ_le_of_lt i.isLt))⟩

end SetLanguage
end JSP000933
