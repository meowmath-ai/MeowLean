import JSP000933ActualLateCollapseHits

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure FixtureKernel {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} (C : SnapshotCarrier T) where
  piece : ∀ n, BlockFixture n → Fin n → Finset ℕ
  subset : ∀ n A i, piece n A i⊆C.bits i.val (fixtureSnapshot A i)
  agrees : ∀ {n N} (hn : n≤N) (A : BlockFixture N) (D : BlockFixture n),
    (∀ i : Fin n, fixtureSnapshot A ⟨i.val,i.isLt.trans_le hn⟩=fixtureSnapshot D i) →
    ∀ i : Fin n, piece N A ⟨i.val,i.isLt.trans_le hn⟩=piece n D i

noncomputable def actualFixtureGluing {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {C : SnapshotCarrier T} (F : FixtureKernel C) (m : ℕ) : B :=
  ⨆ k : Fin (m+1), ⨆ A : BlockFixture (k.val+1),
    fixtureWeight T (k.val+1) A⊓crispFinsetBits (F.piece (k.val+1) A (Fin.last k.val)) m

theorem actualFixtureGluing_last_mask_r379 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {C : SnapshotCarrier T} (F : FixtureKernel C)
    {j : ℕ} (A : BlockFixture (j+1)) (hq : q≤fixtureWeight T (j+1) A) (m : ℕ)
    (hm : m∈C.bits j (fixtureSnapshot A (Fin.last j))) :
    q⊓actualFixtureGluing T F m=q⊓crispFinsetBits (F.piece (j+1) A (Fin.last j)) m := by
  classical
  by_cases hq0 : q=⊥
  · simp [hq0]
  have hQA := hq.trans (fixtureWeight_snapshot_r376 T A (Fin.last j))
  have hj : j≤ m := C.ge_index j (fixtureSnapshot A (Fin.last j)) q hq0 hQA m hm
  apply le_antisymm
  · unfold actualFixtureGluing
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    rw [inf_iSup_eq]
    apply iSup_le
    intro E
    rw [← inf_assoc]
    let w := fixtureWeight T (i.val+1) E
    by_cases hES : m∈F.piece (i.val+1) E (Fin.last i.val)
    · by_cases hZ : q⊓w=⊥
      · change (q⊓w)⊓_≤_
        rw [hZ,bot_inf_eq]
        exact bot_le
      · let r := q⊓w
        have hrA : r≤fixtureWeight T (j+1) A := inf_le_left.trans hq
        have hrE : r≤fixtureWeight T (i.val+1) E := inf_le_right
        by_cases hJ : j=i.val
        · obtain ⟨k,hk⟩ := i
          change j=k at hJ
          subst k
          by_cases hAE : A=E
          · subst E
            exact inf_le_inf_right _ inf_le_left
          · exact False.elim (hZ ((fixtureWeight_disjoint_r376 T _ A E hAE).out r hrA hrE))
        · have hD := hrA.trans (fixtureWeight_snapshot_r376 T A (Fin.last j))
          have hE := hrE.trans (fixtureWeight_snapshot_r376 T E (Fin.last i.val))
          exact False.elim (Finset.disjoint_left.mp (C.cross_disjoint
            (fixtureSnapshot A (Fin.last j)) (fixtureSnapshot E (Fin.last i.val)) r hZ hD hE hJ)
            hm (F.subset _ _ _ hES))
    · simp only [crispFinsetBits,crispTruth,ite_eq_right hES,inf_bot_eq,bot_le]
  · apply le_inf inf_le_left
    apply le_iSup_of_le (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (m+1))
    exact le_iSup_of_le A (le_inf (inf_le_left.trans hq) inf_le_right)

theorem actualFixtureGluing_mask_r379 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {C : SnapshotCarrier T} (F : FixtureKernel C)
    {N : ℕ} (A : BlockFixture N) (i : Fin N) (hq : q≤fixtureWeight T N A)
    (m : ℕ) (hm : m∈C.bits i.val (fixtureSnapshot A i)) :
    q⊓actualFixtureGluing T F m=q⊓crispFinsetBits (F.piece N A i) m := by
  have hi : i.val+1≤N := Nat.succ_le_of_lt i.isLt
  obtain ⟨D,hD,hE⟩ := exists_fixture_prefix_r376 T hi A
  have hA : fixtureSnapshot A i = fixtureSnapshot D (Fin.last i.val) :=
    hE (Fin.last i.val)
  have hP : F.piece N A i = F.piece (i.val+1) D (Fin.last i.val) :=
    F.agrees hi A D hE (Fin.last i.val)
  have hm' : m∈C.bits i.val (fixtureSnapshot D (Fin.last i.val)) := by simpa only [hA] using hm
  rw [hP]
  exact actualFixtureGluing_last_mask_r379 T F D (hq.trans hD) m hm'

theorem actualSourceFixtureGluing_below_r379 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (F : FixtureKernel (sourceSnapshotCarrier T)) :
    p≤bitsBelowValue (actualFixtureGluing T F) (actualSourceUnion T) := by
  apply bitsBelowValue_of_pointwise_r272
  intro m
  apply iSup_le
  intro i
  apply iSup_le
  intro A
  let P := F.piece (i.val+1) A (Fin.last i.val)
  by_cases hm : m∈P
  · exact inf_le_left.trans (snapshot_source_below_union_r368
      (fixtureWeight_snapshot_r376 T A (Fin.last i.val)) m (F.subset _ _ _ hm))
  · simp [P,crispFinsetBits,crispTruth,hm]

end SetLanguage
end JSP000933
