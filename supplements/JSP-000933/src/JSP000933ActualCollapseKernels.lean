import JSP000933ActualFixtureKernelGluing

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def collapseSourceKernel {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : FixtureKernel (sourceSnapshotCarrier T) where
  piece _ A i := (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val)).val
  subset _ A i := Finset.mem_powerset.mp (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val)).property
  agrees hn A D he i := by
    change (collapsePick (fixtureSnapshot A ⟨i.val,i.isLt.trans_le hn⟩) (fixtureGradeAt A i.val)).val=
      (collapsePick (fixtureSnapshot D i) (fixtureGradeAt D i.val)).val
    rw [he i,fixtureGrade_prefix_congr_r377 hn A D he i.val i.isLt.le]

open scoped Classical in
noncomputable def collapseMarkedOutput {n : ℕ} (A : BlockFixture n) (j : ℕ) (i : Fin n) : Finset ℕ :=
  if fixtureHit A i ∧ j≤fixtureGradeAt A i.val then
    (fixtureSnapshot A i).act (collapsePick (fixtureSnapshot A i) (fixtureGradeAt A i.val))
  else ∅

noncomputable def collapseOutputKernel {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (j : ℕ) : FixtureKernel (rangeSnapshotCarrier T) where
  piece _ A i := collapseMarkedOutput A j i
  subset _ A i := by
    classical
    unfold collapseMarkedOutput
    split
    · exact (fixtureSnapshot A i).act_le _
    · exact Finset.empty_subset _
  agrees hn A D he i := by
    classical
    let mark (S : ActualBlockSnapshot i.val) (g : ℕ) :=
      if CollapseBadAt S g ∧ j ≤ g then S.act (collapsePick S g) else ∅
    change mark (fixtureSnapshot A ⟨i.val,i.isLt.trans_le hn⟩) (fixtureGradeAt A i.val) =
      mark (fixtureSnapshot D i) (fixtureGradeAt D i.val)
    rw [he i, fixtureGrade_prefix_congr_r377 hn A D he i.val i.isLt.le]

theorem actualRangeFixtureGluing_below_r380 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (F : FixtureKernel (rangeSnapshotCarrier T)) :
    p≤bitsBelowValue (actualFixtureGluing T F) (actualBlockClamp T) := by
  apply bitsBelowValue_of_pointwise_r272
  intro m
  apply iSup_le
  intro i
  apply iSup_le
  intro A
  let q := fixtureWeight T (i.val+1) A
  let P := F.piece (i.val+1) A (Fin.last i.val)
  let D := fixtureSnapshot A (Fin.last i.val)
  by_cases hm : m∈P
  · have hD : q≤actualBlockSnapshotValue T i.val D := fixtureWeight_snapshot_r376 T A (Fin.last i.val)
    have hR : m∈D.range := F.subset _ _ _ hm
    have h := actualBlockSnapshotValue_range_r367 hD m (D.range_le hR)
    have he : q⊓actualBlockClamp T m=q := by simpa [crispFinsetBits,crispTruth,hR] using h
    exact inf_le_left.trans (he.symm.le.trans inf_le_right)
  · simp [P,crispFinsetBits,crispTruth,hm]

end SetLanguage
end JSP000933
