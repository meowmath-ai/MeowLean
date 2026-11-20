import JSP000933ActualFixtureOutputGeometry

open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

open scoped Classical in
noncomputable def groundFixtureGradePiece {n : ℕ} (A : BlockFixture n) (g : ℕ) : Finset ℕ :=
  if h : ∃ i : Fin n, fixtureHit A i ∧ fixtureGradeAt A i.val=g then
    let i := Classical.choose h
    (fixtureSnapshot A i).act (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val))
  else ∅

theorem groundFixtureGradePiece_budget_r382 {n : ℕ} (A : BlockFixture n) (g N : ℕ) :
    GroundBudgetHolds true (groundFixtureGradePiece A g : Set ℕ) ∅ (dyadicGapDen g) N := by
  classical
  unfold groundFixtureGradePiece
  split
  · rename_i h
    let i := Classical.choose h
    have hi : fixtureHit A i ∧ fixtureGradeAt A i.val=g := Classical.choose_spec h
    let Y := (fixtureSnapshot A i).act (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val))
    change GroundBudgetHolds true (Y : Set ℕ) ∅ (dyadicGapDen g) N
    have hB : GroundBudgetHolds true (Y : Set ℕ) ∅ (dyadicGapDen (fixtureGradeAt A i.val)) N :=
      (collapsePick_bad_spec_r377 hi.1).2 N
    have hc : dyadicGapDen (fixtureGradeAt A i.val)=dyadicGapDen g := congrArg dyadicGapDen hi.2
    exact hc ▸ hB
  · simpa using GroundBudgetHolds.refl_r228 true (∅ : Set ℕ) (dyadicGapDen g) N

theorem groundFixtureGradePiece_hit_r382 {n : ℕ} (A : BlockFixture n) (i : Fin n) (hi : fixtureHit A i) :
    groundFixtureGradePiece A (fixtureGradeAt A i.val)=
      (fixtureSnapshot A i).act (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val)) := by
  classical
  have he : ∃ j : Fin n, fixtureHit A j ∧ fixtureGradeAt A j.val=fixtureGradeAt A i.val :=
    ⟨i,hi,rfl⟩
  unfold groundFixtureGradePiece
  rw [dite_eq_left he]
  have h := Classical.choose_spec he
  rw [fixtureGrade_hit_injective_r377 A h.1 hi h.2]

theorem actualHighGradeOutput_prefixBudget_r382 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (J n : ℕ) :
    p≤nameBudgetValue true (realBitsName (actualFixtureGluing T (collapseOutputKernel T J)))
      (realBitsName (fun _ => ⊥)) (2^J) n := by
  classical
  let G := actualFixtureGluing T (collapseOutputKernel T J)
  have hc := actualRangeFixtureGluing_below_r380 T (collapseOutputKernel T J)
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨A,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (fixtureWeight T (n+1))
    (hqp.trans_eq (fixtureWeight_covers_r376 T (n+1)).symm)
  obtain ⟨S,_,t,ht,htr,hS,_⟩ := exists_joint_crispPrefix_r362 G (fun _ => ⊥) n r hr
  have htA := htr.trans hR
  have htp := htr.trans (hrq.trans hqp)
  let D (i : ℕ) : Set ℕ := groundFixtureGradePiece A (J+i)
  have hCover (m : ℕ) (hm : m<n) (hM : m∈S) :
      m∈({m | ∃ i<n, m∈D i} : Set ℕ) := by
    have he := hS m hm
    have hT : t≤G m := ((show t⊓G m=t by simpa only [crispTruth,ite_eq_left hM,inf_top_eq] using he).symm.le).trans inf_le_right
    have hClamp : t≤actualBlockClamp T m :=
      (le_inf htp hT).trans (bitsBelowValue_apply_r256 hc m)
    rcases fixture_output_at_window_or_zero_r381 T A ht htA m hm.le with ⟨i,hI⟩ | h0
    · let E := fixtureSnapshot A i
      have htE := htA.trans (fixtureWeight_snapshot_r376 T A i)
      have hmE : m∈E.range := by
        have hBit := actualBlockSnapshotValue_range_r367 htE m hI
        exact prop_of_le_crisp_nonzero_r190 ht (((le_inf le_rfl hClamp).trans_eq hBit).trans inf_le_right)
      have hBit := actualFixtureGluing_mask_r379 T (collapseOutputKernel T J) A i htA m hmE
      have hZ : m∈collapseMarkedOutput A J i := prop_of_le_crisp_nonzero_r190 ht
        (((le_inf le_rfl hT).trans_eq hBit).trans inf_le_right)
      have hMark : fixtureHit A i ∧ J≤fixtureGradeAt A i.val := by
        by_contra hNo
        simp [collapseMarkedOutput,hNo] at hZ
      let d := fixtureGradeAt A i.val-J
      have hd : J+d=fixtureGradeAt A i.val := Nat.add_sub_of_le hMark.2
      have hiM := (rangeSnapshotCarrier T).ge_index i.val E t ht htE m hmE
      have hD : d<n := (Nat.sub_le _ _).trans_lt
        ((fixtureGrade_le_index_r377 A i.val).trans_lt (hiM.trans_lt hm))
      refine ⟨d,hD,?_⟩
      simpa only [D,hd,groundFixtureGradePiece_hit_r382 A i hMark.1,Finset.mem_coe] using
        (show m∈(fixtureSnapshot A i).act (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val)) by
          simpa only [collapseMarkedOutput,ite_eq_left hMark] using hZ)
    · exact False.elim (ht (le_bot_iff.mp ((le_inf le_rfl hClamp).trans_eq h0)))
  have hMass (i : ℕ) (_ : i<n) :
      ((2:ℕ)^i*(2*(2:ℕ)^J))*groundBudgetMass true n (D i)≤groundBudgetDenom true n := by
    have hc : (2:ℕ)^i*(2*(2:ℕ)^J)=dyadicGapDen (J+i) := by unfold dyadicGapDen; rw [pow_succ,pow_add]; ring
    rw [hc]
    have h := groundFixtureGradePiece_budget_r382 A (J+i) n
    rwa [groundBudgetHolds_weighted_r232,Set.sdiff_empty] at h
  have hG : GroundBudgetHolds true S ∅ (2^J) n := by
    rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
    apply (Nat.mul_le_mul_left _ ((groundBudgetMass_prefix_mono_r341 true n hCover).trans
      (groundBudgetMass_finite_union_r343 true n D n))).trans
    exact dyadic_natBudget_sum_r343 (groundBudgetDenom true n) n (2^J) (fun i => groundBudgetMass true n (D i)) hMass
  have h0 (m : ℕ) (hm : m<n) : t⊓(⊥ : B)=t⊓crispTruth B (m∈(∅ : Set ℕ)) := by simp [crispTruth]
  have hC := nameBudgetValue_crispPrefix_mask_r340 true (2^J) n hS h0
  have hT : t≤crispTruth B (GroundBudgetHolds true S ∅ (2^J) n) := by simp [crispTruth,hG]
  exact ⟨t,ht,htr.trans hrq,((le_inf le_rfl hT).trans_eq hC.symm).trans inf_le_right⟩

end SetLanguage
end JSP000933
