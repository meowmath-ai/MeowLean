import JSP000933ActualUniqueBlockSnapshots

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem snapshot_act_arbitrary_r368 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D : ActualBlockSnapshot k}
    (hC : NamedContinuousOn p L) (hD : q≤actualBlockSnapshotValue T k D)
    (x : ℕ → B) (a : BlockInput D.history)
    (hx : ∀ m∈blockSnapshotSource D.history, q⊓x m=q⊓crispFinsetBits a.val m)
    (m : ℕ) (hm : m∈groundStageWindow D.history k) :
    q⊓actualClampedOutput T x m=q⊓crispFinsetBits (D.act a) m :=
  (actualClampedOutput_local_r365 T hC D.history (actualBlockSnapshotValue_history_r367 hD)
      x (crispFinsetBits a.val) k m (by omega) hm hx).trans
    (actualBlockSnapshotValue_act_r367 hD a m hm)

theorem snapshots_common_geometry_r368 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {j k : ℕ} {D : ActualBlockSnapshot j} {E : ActualBlockSnapshot k}
    (hN : q≠⊥) (hD : q≤actualBlockSnapshotValue T j D) (hE : q≤actualBlockSnapshotValue T k E)
    (hjk : j≠k) :
    Disjoint (blockSnapshotSource D.history) (blockSnapshotSource E.history) ∧
      Disjoint (groundStageWindow D.history j) (groundStageWindow E.history k) := by
  let N := max (j+2) (k+2)
  have hDL : j+2≤N := le_max_left _ _
  have hEL : k+2≤N := le_max_right _ _
  obtain ⟨H,r,hr,hrq,hrH,hD'⟩ := T.exists_larger_snapshot_r357 hDL D.history hN
    (actualBlockSnapshotValue_history_r367 hD)
  have hA : (T.level N).weight H≠⊥ := fun he => hr (le_bot_iff.mp (hrH.trans_eq he))
  have hg := T.good_history_r354 H hA
  have hE' := T.snapshots_agree_r357 hEL E.history H hr
    (hrq.trans (actualBlockSnapshotValue_history_r367 hE)) hrH
  have hJ : j+1<N := by omega
  have hK : k+1<N := by omega
  constructor
  · apply Finset.disjoint_left.mpr
    intro m hM hM'
    have hS : m∈justSourceBlock (historyStage H j).position := by
      simpa only [hD' j (by omega),blockSnapshotSource] using hM
    have hS' : m∈justSourceBlock (historyStage H k).position := by
      simpa only [hE' k (by omega),blockSnapshotSource] using hM'
    rcases lt_or_gt_of_ne hjk with he | he
    · exact (not_lt_of_ge ((hg k (by omega)).2.1.trans (hg.source_after_right_r354 (by omega) hS')))
        (hg.source_before_laterLeft_r354 he (by omega) hS)
    · exact (not_lt_of_ge ((hg j (by omega)).2.1.trans (hg.source_after_right_r354 (by omega) hS)))
        (hg.source_before_laterLeft_r354 he (by omega) hS')
  · apply Finset.disjoint_left.mpr
    intro m hM hM'
    have hW : m∈groundStageWindow H j := by
      simpa only [groundStageWindow,hD' j (by omega),hD' (j+1) (by omega)] using hM
    have hW' : m∈groundStageWindow H k := by
      simpa only [groundStageWindow,hE' k (by omega),hE' (k+1) (by omega)] using hM'
    exact hjk (hg.window_unique_r357 hJ hK hW hW')

theorem snapshot_source_below_union_r368 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D : ActualBlockSnapshot k}
    (hD : q≤actualBlockSnapshotValue T k D) (m : ℕ) (hm : m∈blockSnapshotSource D.history) :
    q≤actualSourceUnion T m := by
  apply le_of_dense_named_refinements_r219
  intro s hs hsq
  let N := max (k+2) (m+1)
  have hn : k+2≤N := le_max_left _ _
  obtain ⟨H,r,hr,hrs,hrH,hA⟩ := T.exists_larger_snapshot_r357 hn D.history hs
    (hsq.trans (actualBlockSnapshotValue_history_r367 hD))
  have hW : (T.level N).weight H≠⊥ := fun he => hr (le_bot_iff.mp (hrH.trans_eq he))
  have hg := T.good_history_r354 H hW
  have hM : m∈justSourceBlock (historyStage H k).position := by simpa only [hA k (by omega),blockSnapshotSource] using hm
  have he : historySourceDigit H m := ⟨k,hg.source_ge_index_r354 (by omega) hM,hM⟩
  have hE := mask_under_r302 hrH (actualSourceUnion_mask_r355 T H m
    ((Nat.lt_succ_self m).trans_le (le_max_right (k+2) (m+1))))
  have hR : r⊓actualSourceUnion T m=r := by simpa only [crispTruth,ite_eq_left he,inf_top_eq] using hE
  exact ⟨r,hr,hrs,hR.symm.le.trans inf_le_right⟩

end SetLanguage
end JSP000933
