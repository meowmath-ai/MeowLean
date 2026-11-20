import JSP000933ActualCollapseGradeSchedule

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualNoCollapseValue {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : B :=
  ⨆ g : ℕ, eventuallyStageValue (fun j => snapshotPropValue T j (fun D => ¬CollapseBadAt D g))

theorem fixtureSnapshots_agree_r378 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (hn : n≤N) (C : BlockFixture n) (A : BlockFixture N)
    (hq : q≠⊥) (hC : q≤fixtureWeight T n C) (hA : q≤fixtureWeight T N A) :
    ∀ i : Fin n, fixtureSnapshot A ⟨i.val,i.isLt.trans_le hn⟩=fixtureSnapshot C i := by
  obtain ⟨C',hW,hE⟩ := exists_fixture_prefix_r376 T hn A
  by_cases he : C'=C
  · subst C'
    exact hE
  · exact (hq ((fixtureWeight_disjoint_r376 T n C' C he).out q (hA.trans hW) hC)).elim

theorem badCollapse_possible_late_r378 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hqp : q≤p) (hF : q≤(actualNoCollapseValue T)ᶜ)
    (g N : ℕ) :
    q≤⨆ j : {j : ℕ // N≤j}, snapshotPropValue T j.val (fun D => CollapseBadAt D g) := by
  let A (j : ℕ) := snapshotPropValue T j (fun D => ¬CollapseBadAt D g)
  have hA : q≤(⨅ j : {j : ℕ // N≤j}, A j.val)ᶜ := hF.trans
    (compl_le_compl ((le_iSup (fun N : ℕ => ⨅ j : {j : ℕ // N≤j},A j.val) N).trans
      (le_iSup (fun g : ℕ => eventuallyStageValue
        (fun j => snapshotPropValue T j (fun D => ¬CollapseBadAt D g))) g)))
  rw [compl_iInf] at hA
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  obtain ⟨j,r,hr,hrs,hR⟩ := exists_nonzero_below_choice_r135 s hs
    (fun j : {j : ℕ // N≤j} => (A j.val)ᶜ) (hsq.trans hA)
  have hrp := hrs.trans (hsq.trans hqp)
  obtain ⟨D,t,ht,htr,hD⟩ := exists_nonzero_below_choice_r135 r hr (actualBlockSnapshotValue T j.val)
    (hrp.trans (actualBlockSnapshots_cover_r366 T j.val))
  have hBad : CollapseBadAt D g := by
    by_contra hn
    have hB : t≤A j.val := le_iSup_of_le D (le_inf hD (by simp [crispTruth,hn]))
    exact ht (le_bot_iff.mp ((le_inf hB (htr.trans hR)).trans_eq inf_compl_eq_bot'))
  exact ⟨t,ht,htr.trans hrs,le_iSup_of_le j (le_iSup_of_le D (le_inf hD (by simp [crispTruth,hBad])))⟩

theorem fixtureGrade_constant_of_no_hit_r378 {n : ℕ} (A : BlockFixture n) (a : ℕ) :
    ∀ b, a≤b → b≤n →
      (∀ i : Fin n, a≤ i.val → i.val<b → ¬fixtureHit A i) → fixtureGradeAt A b=fixtureGradeAt A a := by
  intro b
  induction b with
  | zero => intro hA _ _; rw [Nat.eq_zero_of_le_zero hA]
  | succ b ih =>
    intro hA hb hM
    by_cases he : a=b+1
    · rw [he]
    · have hAB : a≤b := by omega
      have hBn : b<n := Nat.lt_of_succ_le hb
      exact (fixtureGrade_miss_r377 A ⟨b,hBn⟩ (hM ⟨b,hBn⟩ hAB (Nat.lt_succ_self b))).trans
        (ih hAB hBn.le (fun i hi hj => hM i hi (hj.trans (Nat.lt_succ_self b))))

theorem exists_actualLateHit_refinement_r378 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hq : q≠⊥) (hqp : q≤p) (hF : q≤(actualNoCollapseValue T)ᶜ)
    (N : ℕ) :
    ∃ (n : ℕ) (A : BlockFixture n) (i : Fin n) (r : B),
      r≠⊥ ∧ r≤q ∧ r≤fixtureWeight T n A ∧ N≤ i.val ∧ fixtureHit A i := by
  obtain ⟨C,s,hs,hsq,hC⟩ := exists_nonzero_below_choice_r135 q hq (fixtureWeight T N)
    (hqp.trans_eq (fixtureWeight_covers_r376 T N).symm)
  let g := fixtureGradeAt C N
  obtain ⟨j,t,ht,hts,hT⟩ := exists_nonzero_below_choice_r135 s hs
    (fun j : {j : ℕ // N≤j} => snapshotPropValue T j.val (fun D => CollapseBadAt D g))
    (hsq.trans (badCollapse_possible_late_r378 T hqp hF g N))
  obtain ⟨D,u,hu,hut,hD⟩ := exists_nonzero_below_choice_r135 t ht
    (fun D : ActualBlockSnapshot j.val => actualBlockSnapshotValue T j.val D⊓crispTruth B (CollapseBadAt D g)) hT
  have hBad : CollapseBadAt D g := prop_of_le_crisp_nonzero_r190 hu (hD.trans inf_le_right)
  have huS := hut.trans hts
  have huP := huS.trans (hsq.trans hqp)
  obtain ⟨A,r,hr,hru,hA⟩ := exists_nonzero_below_choice_r135 u hu (fixtureWeight T (j.val+1))
    (huP.trans_eq (fixtureWeight_covers_r376 T (j.val+1)).symm)
  have hrS := hru.trans huS
  have hNJ : N≤j.val+1 := j.property.trans (Nat.le_succ _)
  have hE := fixtureSnapshots_agree_r378 T hNJ C A hr (hrS.trans hC) hA
  have hG : fixtureGradeAt A N=g := fixtureGrade_prefix_congr_r377 hNJ A C hE N le_rfl
  have hLast : fixtureSnapshot A (Fin.last j.val)=D :=
    actualBlockSnapshot_unique_r367 hr
      (hA.trans (fixtureWeight_snapshot_r376 T A (Fin.last j.val))) (hru.trans (hD.trans inf_le_left))
  by_cases hHit : ∃ i : Fin (j.val+1), N≤ i.val ∧ fixtureHit A i
  · obtain ⟨i,hi,hI⟩ := hHit
    exact ⟨j.val+1,A,i,r,hr,hrS.trans hsq,hA,hi,hI⟩
  · have hGrade : fixtureGradeAt A j.val=g :=
      (fixtureGrade_constant_of_no_hit_r378 A N j.val j.property (Nat.le_succ _)
        (fun i hi _ h => hHit ⟨i,hi,h⟩)).trans hG
    have hI : fixtureHit A (Fin.last j.val) := by
      unfold fixtureHit
      rw [hLast]
      change CollapseBadAt D (fixtureGradeAt A j.val)
      rw [hGrade]
      exact hBad
    exact False.elim (hHit ⟨Fin.last j.val,j.property,hI⟩)

end SetLanguage
end JSP000933
