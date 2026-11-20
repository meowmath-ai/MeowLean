import JSP000933ActualSnapshotsCrossGeometry

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure SnapshotCarrier {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L) where
  bits : ∀ k, ActualBlockSnapshot k → Finset ℕ
  ge_index : ∀ k (D : ActualBlockSnapshot k) (q : B), q≠⊥ → q≤actualBlockSnapshotValue T k D →
    ∀ m∈bits k D, k≤ m
  cross_disjoint : ∀ {j k} (D : ActualBlockSnapshot j) (E : ActualBlockSnapshot k) (q : B),
    q≠⊥ → q≤actualBlockSnapshotValue T j D → q≤actualBlockSnapshotValue T k E →
    j≠k → Disjoint (bits j D) (bits k E)

def sourceSnapshotCarrier {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : SnapshotCarrier T where
  bits _ D := blockSnapshotSource D.history
  ge_index k D q hq hd m hm := by
    have hH := actualBlockSnapshotValue_history_r367 hd
    have hw : (T.level (k+2)).weight D.history≠⊥ := fun he => hq (le_bot_iff.mp (hH.trans_eq he))
    exact (T.good_history_r354 D.history hw).source_ge_index_r354 (by omega) hm
  cross_disjoint D E q hq hd he hk := (snapshots_common_geometry_r368 hq hd he hk).1

def rangeSnapshotCarrier {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : SnapshotCarrier T where
  bits _ D := D.range
  ge_index k D q hq hd m hm := by
    have hH := actualBlockSnapshotValue_history_r367 hd
    have hw : (T.level (k+2)).weight D.history≠⊥ := fun he => hq (le_bot_iff.mp (hH.trans_eq he))
    exact ((T.good_history_r354 D.history hw).out_ge_index_r354 k (by omega)).trans
      (Finset.mem_Ico.mp (D.range_le hm)).1
  cross_disjoint D E q hq hd he hk :=
    Disjoint.mono D.range_le E.range_le (snapshots_common_geometry_r368 hq hd he hk).2

noncomputable def actualSnapshotGluing {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (F : ∀ k, ActualBlockSnapshot k → Finset ℕ) (m : ℕ) : B :=
  ⨆ k : Fin (m+1), ⨆ D : ActualBlockSnapshot k.val,
    actualBlockSnapshotValue T k.val D⊓crispFinsetBits (F k.val D) m

theorem actualSnapshotGluing_mask_r369 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (C : SnapshotCarrier T)
    (F : ∀ k, ActualBlockSnapshot k → Finset ℕ) (hF : ∀ k D, F k D⊆C.bits k D)
    {j : ℕ} (D : ActualBlockSnapshot j) (hq : q≤actualBlockSnapshotValue T j D)
    (m : ℕ) (hm : m∈C.bits j D) :
    q⊓actualSnapshotGluing T F m=q⊓crispFinsetBits (F j D) m := by
  classical
  by_cases hq0 : q=⊥
  · simp [hq0]
  have hj : j≤ m := C.ge_index j D q hq0 hq m hm
  apply le_antisymm
  · unfold actualSnapshotGluing
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    rw [inf_iSup_eq]
    apply iSup_le
    intro E
    rw [← inf_assoc]
    by_cases hES : m∈F i.val E
    · by_cases hZ : q⊓actualBlockSnapshotValue T i.val E=⊥
      · rw [hZ,bot_inf_eq]
        exact bot_le
      · let r := q⊓actualBlockSnapshotValue T i.val E
        have hrD : r≤actualBlockSnapshotValue T j D := inf_le_left.trans hq
        have hrE : r≤actualBlockSnapshotValue T i.val E := inf_le_right
        by_cases hJ : j=i.val
        · obtain ⟨k,hk⟩ := i
          change j=k at hJ
          subst k
          have he : D=E := actualBlockSnapshot_unique_r367 hZ hrD hrE
          subst E
          exact inf_le_inf_right _ inf_le_left
        · exact False.elim (Finset.disjoint_left.mp (C.cross_disjoint D E r hZ hrD hrE hJ)
            hm (hF i.val E hES))
    · simp only [crispFinsetBits,crispTruth,ite_eq_right hES,inf_bot_eq,bot_le]
  · apply le_inf inf_le_left
    apply le_iSup_of_le (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (m+1))
    exact le_iSup_of_le D (le_inf (inf_le_left.trans hq) inf_le_right)

theorem actualSnapshotGluing_below_source_r369 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (F : ∀ k, ActualBlockSnapshot k → Finset ℕ)
    (hF : ∀ k D, F k D⊆blockSnapshotSource D.history) :
    p≤bitsBelowValue (actualSnapshotGluing T F) (actualSourceUnion T) := by
  apply bitsBelowValue_of_pointwise_r272
  intro m
  apply iSup_le
  intro k
  apply iSup_le
  intro D
  by_cases hm : m∈F k.val D
  · exact inf_le_left.trans (snapshot_source_below_union_r368 (q := actualBlockSnapshotValue T k.val D)
      le_rfl m (hF k.val D hm))
  · simp [crispFinsetBits,crispTruth,hm]

theorem actualSnapshotGluing_below_range_r369 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (F : ∀ k, ActualBlockSnapshot k → Finset ℕ)
    (hF : ∀ k D, F k D⊆D.range) :
    p≤bitsBelowValue (actualSnapshotGluing T F) (actualBlockClamp T) := by
  apply bitsBelowValue_of_pointwise_r272
  intro m
  apply iSup_le
  intro k
  apply iSup_le
  intro D
  let q := actualBlockSnapshotValue T k.val D
  by_cases hm : m∈F k.val D
  · have h := actualBlockSnapshotValue_range_r367 (q := q) le_rfl m (D.range_le (hF k.val D hm))
    have he : q⊓actualBlockClamp T m=q := by simpa [crispFinsetBits,crispTruth,hF k.val D hm] using h
    exact inf_le_left.trans (he.symm.le.trans inf_le_right)
  · simp [crispFinsetBits,crispTruth,hm]

end SetLanguage
end JSP000933
