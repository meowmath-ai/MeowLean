import JSP000933ActualHighGradeBudget

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem dominatedProfile_zero_under_mask_r383 {p q : B} {a b : ℕ → B}
    (h : p≤bitsBelowValue a b) (hq : q≤p) (m : ℕ) (hb : q⊓b m=⊥) : q⊓a m=⊥ := by
  apply le_bot_iff.mp
  exact (le_inf inf_le_left ((inf_le_inf_right (a m) hq).trans (bitsBelowValue_apply_r256 h m))).trans_eq hb

theorem actualHighGradeOutput_lateAgreement_r383 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (A : BlockFixture (N+1))
    (hA : q≤fixtureWeight T (N+1) A) (J : ℕ) (hJ : J≤fixtureGradeAt A N) :
    ∀ m≥(historyStage A.2.history N).out,
      q⊓actualFixtureGluing T (collapseOutputKernel T 0) m=
        q⊓actualFixtureGluing T (collapseOutputKernel T J) m := by
  intro m hm
  let F₀ := collapseOutputKernel T 0
  let F₁ := collapseOutputKernel T J
  let x := actualFixtureGluing T F₀
  let y := actualFixtureGluing T F₁
  have hxP := actualRangeFixtureGluing_below_r380 T F₀
  have hyP := actualRangeFixtureGluing_below_r380 T F₁
  apply (le_bitEq_iff_r126 _ _ _).mp
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  let K := max N m
  have hKP : N+1≤K+1 := Nat.succ_le_succ (le_max_left _ _)
  have hsP := hsq.trans (hA.trans (fixtureWeight_le_r376 T (N+1) A))
  obtain ⟨D,r,hr,hrs,hRD⟩ := exists_nonzero_below_choice_r135 s hs (fixtureWeight T (K+1))
    (hsP.trans_eq (fixtureWeight_covers_r376 T (K+1)).symm)
  have hrP := hrs.trans hsP
  have hA' := fixtureSnapshots_agree_r378 T hKP A D hr (hrs.trans (hsq.trans hA)) hRD
  let H := D.2.history
  have hH := fixture_mainHistory_mask_r381 T D hRD
  have hh : (T.level (K+2)).weight H≠⊥ := fun h => hr (le_bot_iff.mp (hH.trans_eq h))
  have hGood := T.good_history_r354 H hh
  have hGrade : J≤fixtureGradeAt D N := hJ.trans_eq
    (fixtureGrade_prefix_congr_r377 hKP D A hA' N (Nat.le_succ N)).symm
  have hOut : (historyStage H N).out=(historyStage A.2.history N).out := by
    let i : Fin (K+1) := ⟨N,Nat.lt_succ_of_le (le_max_left N m)⟩
    have he : fixtureSnapshot D i=A.2 :=
      (hA' (Fin.last N)).trans (fixtureSnapshot_last_r376 A)
    have hE := fixture_snapshotGeometry_r381 T D hr hRD i N (by simp [i])
    exact congrArg ActualGroundStage.out (hE.trans (congrArg (fun d : ActualBlockSnapshot N =>
      historyStage d.history N) he))
  have hZero (h : r⊓actualBlockClamp T m=⊥) : r⊓x m=r⊓y m :=
    (dominatedProfile_zero_under_mask_r383 hxP hrP m h).trans (dominatedProfile_zero_under_mask_r383 hyP hrP m h).symm
  suffices he : r⊓x m=r⊓y m from ⟨r,hr,hrs,(le_bitEq_iff_r126 _ _ _).mpr he⟩
  rcases fixture_output_at_window_or_zero_r381 T D hr hRD m (le_max_right _ _) with ⟨i,hi⟩ | h0
  · let E := fixtureSnapshot D i
    have hrE := hRD.trans (fixtureWeight_snapshot_r376 T D i)
    by_cases hR : m∈E.range
    · have hI : N≤ i.val := by
        by_contra hn
        have hLt : i.val<N := Nat.lt_of_not_ge hn
        have hw := (Finset.mem_Ico.mp hi).2
        have he := fixture_snapshotGeometry_r381 T D hr hRD i (i.val+1) (by omega)
        have hw' : m<(historyStage H (i.val+1)).out := by
          change m < (historyStage D.2.history (i.val+1)).out
          rw [he]
          exact hw
        have hN : (historyStage H (i.val+1)).out≤(historyStage H N).out := by
          rcases eq_or_lt_of_le (Nat.succ_le_of_lt hLt) with heq | hlt
          · have heq' : i.val + 1 = N := heq
            rw [heq']
          · exact (hGood.out_increases_r354 hlt (by have hL := le_max_left N m; omega)).le
        exact not_lt_of_ge (hN.trans (hOut.le.trans hm)) hw'
      have hIJ : J≤fixtureGradeAt D i.val := hGrade.trans (fixtureGrade_mono_r377 D hI)
      have hx := actualFixtureGluing_mask_r379 T F₀ D i hRD m hR
      have hy := actualFixtureGluing_mask_r379 T F₁ D i hRD m hR
      have he : collapseMarkedOutput D 0 i=collapseMarkedOutput D J i := by
        by_cases h : fixtureHit D i <;> simp [collapseMarkedOutput,h,hIJ]
      exact hx.trans ((congrArg (fun z : Finset ℕ => r⊓crispFinsetBits z m) he).trans hy.symm)
    · change m ∉ (fixtureSnapshot D i).range at hR
      have hBit := actualBlockSnapshotValue_range_r367 hrE m hi
      exact hZero (by simpa only [crispFinsetBits, crispTruth, ite_eq_right hR, inf_bot_eq] using hBit)
  · exact hZero h0

theorem actualHighGradeOutput_harmEq_on_bad_r383 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hqp : q≤p) (hB : q≤(actualNoCollapseValue T)ᶜ) (J : ℕ) :
    LocalEq true q (actualFixtureGluing T (collapseOutputKernel T 0))
      (actualFixtureGluing T (collapseOutputKernel T J)) := by
  let x := actualFixtureGluing T (collapseOutputKernel T 0)
  let y := actualFixtureGluing T (collapseOutputKernel T J)
  suffices H : q≤liveLE true x y⊓liveLE true y x from ⟨H.trans inf_le_left,H.trans inf_le_right⟩
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  obtain ⟨N,A,r,hr,hrs,hRA,hJ⟩ := exists_actualGradeAtLeast_refinement_r381 T hs (hsq.trans hqp) (hsq.trans hB) J
  have hrp := hrs.trans (hsq.trans hqp)
  obtain ⟨D,t,ht,htr,hTD⟩ := exists_nonzero_below_choice_r135 r hr (fixtureWeight T (N+1))
    (hrp.trans_eq (fixtureWeight_covers_r376 T (N+1)).symm)
  have hE := fixtureSnapshots_agree_r378 T (Nat.le_succ N) A D ht (htr.trans hRA) hTD
  have hJD : J≤fixtureGradeAt D N := hJ.trans_eq
    (fixtureGrade_prefix_congr_r377 (Nat.le_succ N) D A hE N le_rfl).symm
  have H := harmonicLocalEq_late_agreement_r341 (p := t) x y _ (actualHighGradeOutput_lateAgreement_r383 T D hTD J hJD)
  exact ⟨t,ht,htr.trans hrs,le_inf H.1 H.2⟩

end SetLanguage
end JSP000933
