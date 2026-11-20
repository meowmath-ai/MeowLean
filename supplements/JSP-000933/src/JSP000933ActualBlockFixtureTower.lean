import JSP000933ActualApproxEveryRangeSubset

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def BlockFixture : ℕ → Type
  | 0 => PUnit
  | n+1 => BlockFixture n × ActualBlockSnapshot n

noncomputable def fixtureWeight {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : (n : ℕ) → BlockFixture n → B
  | 0, _ => p
  | n+1, A => fixtureWeight T n A.1⊓actualBlockSnapshotValue T n A.2

def fixtureSnapshot : {n : ℕ} → BlockFixture n → (i : Fin n) → ActualBlockSnapshot i.val
  | 0, _, i => Fin.elim0 i
  | n+1, A, i => Fin.lastCases A.2 (fun j => fixtureSnapshot A.1 j) i

@[simp] theorem fixtureSnapshot_last_r376 {n : ℕ} (A : BlockFixture (n+1)) :
    fixtureSnapshot A (Fin.last n)=A.2 := by simp [fixtureSnapshot]

theorem fixtureSnapshot_before_r376 {n : ℕ} (A : BlockFixture (n+1)) (i : Fin n) :
    fixtureSnapshot A i.castSucc=fixtureSnapshot A.1 i := by simp [fixtureSnapshot]

theorem fixtureWeight_le_r376 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (n : ℕ) (A : BlockFixture n) : fixtureWeight T n A≤p := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact inf_le_left.trans (ih A.1)

theorem fixtureWeight_snapshot_r376 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n : ℕ} (A : BlockFixture n) (i : Fin n) :
    fixtureWeight T n A≤actualBlockSnapshotValue T i.val (fixtureSnapshot A i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [fixtureSnapshot_last_r376, Fin.val_last] using
        (show fixtureWeight T (n+1) A≤actualBlockSnapshotValue T n A.2 from inf_le_right)
    · rw [fixtureSnapshot_before_r376]
      exact (show fixtureWeight T (n+1) A≤fixtureWeight T n A.1 from inf_le_left).trans (ih A.1 j)

theorem fixtureWeight_covers_r376 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (n : ℕ) : (⨆ A, fixtureWeight T n A)=p := by
  induction n with
  | zero =>
    exact le_antisymm (iSup_le (fun _ => le_rfl))
      (le_iSup (fixtureWeight T 0) PUnit.unit)
  | succ n ih =>
    apply le_antisymm (iSup_le (fixtureWeight_le_r376 T (n+1)))
    have hd : (⨆ D, actualBlockSnapshotValue T n D) = p :=
      (actualBlockSnapshotPartition T n).covers
    calc
      p = p ⊓ p := (inf_idem (a := p)).symm
      _ = (⨆ A, fixtureWeight T n A) ⊓ (⨆ D, actualBlockSnapshotValue T n D) := by
        rw [ih, hd]
      _ ≤ ⨆ A : BlockFixture (n+1), fixtureWeight T (n+1) A := by
        rw [iSup_inf_iSup] <;> exact le_rfl

theorem fixtureWeight_disjoint_r376 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (n : ℕ) (A C : BlockFixture n) (hn : A≠C) :
    Disjoint (fixtureWeight T n A) (fixtureWeight T n C) := by
  induction n with
  | zero =>
    change PUnit at A C
    exact (hn (Subsingleton.elim A C)).elim
  | succ n ih =>
    by_cases he : A.1=C.1
    · have hD : A.2≠C.2 := fun hD => hn (Prod.ext he hD)
      exact ((actualBlockSnapshotPartition T n).separate _ _ hD).mono inf_le_right inf_le_right
    · exact (ih A.1 C.1 he).mono inf_le_left inf_le_left

noncomputable def fixturePartition {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (n : ℕ) : IndexedPartition B (BlockFixture n) p :=
  ⟨fixtureWeight T n,fixtureWeight_covers_r376 T n,fixtureWeight_disjoint_r376 T n⟩

theorem exists_fixture_prefix_r376 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {n N : ℕ} (h : n≤N) (A : BlockFixture N) :
    ∃ C : BlockFixture n, fixtureWeight T N A≤fixtureWeight T n C ∧
      ∀ i : Fin n, fixtureSnapshot A ⟨i.val,i.isLt.trans_le h⟩=fixtureSnapshot C i := by
  induction N with
  | zero =>
    have he : n=0 := Nat.eq_zero_of_le_zero h
    subst n
    exact ⟨A,le_rfl,fun i => Fin.elim0 i⟩
  | succ N ih =>
    by_cases he : n=N+1
    · subst n
      exact ⟨A,le_rfl,fun _ => rfl⟩
    · have hN : n≤N := by omega
      obtain ⟨C,hC,hEq⟩ := ih hN A.1
      refine ⟨C,inf_le_left.trans hC,?_⟩
      intro i
      exact (fixtureSnapshot_before_r376 A ⟨i.val,i.isLt.trans_le hN⟩).trans (hEq i)

end SetLanguage
end JSP000933
