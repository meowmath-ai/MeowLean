import JSP000933ActualMeetDefectDiagonal

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def emptyBlockInput {k : ℕ} (H : ActualStageHistory (k+2)) : BlockInput H :=
  ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩

noncomputable def snapshotPropValue {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (j : ℕ) (P : ActualBlockSnapshot j → Prop) : B :=
  ⨆ D : ActualBlockSnapshot j, actualBlockSnapshotValue T j D⊓crispTruth B (P D)

theorem snapshotPropValue_mono_r372 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (j : ℕ) {P Q : ActualBlockSnapshot j → Prop} (h : ∀ D, P D → Q D) :
    snapshotPropValue T j P ≤ snapshotPropValue T j Q := by
  classical
  apply iSup_le
  intro D
  apply le_iSup_of_le D
  apply inf_le_inf_left
  by_cases hp : P D
  · simp [crispTruth,hp,h D hp]
  · simp [crispTruth,hp]

theorem eventuallyStageValue_mono_r372 {G H : ℕ → B} (h : ∀ j, G j≤H j) :
    eventuallyStageValue G≤eventuallyStageValue H := by
  apply iSup_le
  intro N
  apply le_iSup_of_le N
  exact le_iInf (fun j => (iInf_le _ j).trans (h j.val))

theorem eventuallyStageValue_join_r372 (G H : ℕ → B) :
    eventuallyStageValue G⊓eventuallyStageValue H≤eventuallyStageValue (fun j => G j⊓H j) := by
  unfold eventuallyStageValue
  rw [iSup_inf_iSup]
  apply iSup_le
  rintro ⟨N,M⟩
  apply le_iSup_of_le (max N M)
  apply le_iInf
  intro j
  have hN : N≤j.val := (le_max_left N M).trans j.property
  have hM : M≤j.val := (le_max_right N M).trans j.property
  exact le_inf (inf_le_left.trans (iInf_le
    (fun i : {i : ℕ // N ≤ i} => G i.val) ⟨j.val,hN⟩))
    (inf_le_right.trans (iInf_le
      (fun i : {i : ℕ // M ≤ i} => H i.val) ⟨j.val,hM⟩))

theorem actualEmptyImage_eventuallyBudget_r372 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x))) (k : ℕ) (hk : k≠0) :
    p≤eventuallyStageValue (fun j => snapshotPieceGoodValue T true k j
      (fun D => D.act (emptyBlockInput D.history))) := by
  let z : ℕ → B := fun _ => ⊥
  have hz : p≤bitsBelowValue z (actualSourceUnion T) := bitsBelowValue_of_pointwise_r272 (fun _ => bot_le)
  have hNull := (actualClampedOutput_harmEq_r364 F T hL z hz).trans_r236
    (F.restrict_r246 (show p≤p from le_rfl)).mapBot_r237
  apply namedNull_containedSnapshot_eventuallyBudget_r370 T (rangeSnapshotCarrier T) true k hk
    (actualClampedOutput T z) hNull.1 _ (fun _ D => D.act_le _)
  intro j D m hm
  let q := actualBlockSnapshotValue T j D
  have he := actualBlockSnapshotValue_act_r367 (q := q) le_rfl (emptyBlockInput D.history) m (D.range_le (D.act_le _ hm))
  have hz0 : crispFinsetBits (B := B) (emptyBlockInput D.history).val=z := by
    funext i
    simp [emptyBlockInput,crispFinsetBits,crispTruth,z]
  rw [hz0] at he
  have hh : q⊓actualClampedOutput T z m=q := by
    simpa only [crispFinsetBits,crispTruth,ite_eq_left hm,inf_top_eq] using he
  exact hh.symm.le.trans inf_le_right

theorem actualAllMeetDefects_eventuallyBudget_r372 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (k : ℕ) (hk : k≠0) :
    p≤eventuallyStageValue (fun j => snapshotPropValue T j
      (fun D => ∀ x y, GroundAllBudgets true k (snapshotActMeetDefect D x y))) := by
  classical
  let Good (j : ℕ) (D : ActualBlockSnapshot j) (xy : BlockInput D.history×BlockInput D.history) :=
    GroundAllBudgets true k (snapshotActMeetDefect D xy.1 xy.2)
  let pick (j : ℕ) (D : ActualBlockSnapshot j) : BlockInput D.history×BlockInput D.history :=
    if h : ∃ xy, ¬Good j D xy then Classical.choose h else (emptyBlockInput D.history,emptyBlockInput D.history)
  have hPick (j : ℕ) (D : ActualBlockSnapshot j) (hh : Good j D (pick j D)) : ∀ xy, Good j D xy := by
    intro xy
    by_contra hn
    have he : ∃ xy, ¬Good j D xy := ⟨xy,hn⟩
    have hbad := Classical.choose_spec he
    exact hbad (by simpa only [pick,dite_eq_left he] using hh)
  apply (actualChosenMeetDefect_eventuallyBudget_r371 F T hC hL k hk
    (fun j D => (pick j D).1) (fun j D => (pick j D).2)).trans
  apply eventuallyStageValue_mono_r372
  intro j
  exact snapshotPropValue_mono_r372 T j (fun D h x y => hPick j D h (x,y))

end SetLanguage
end JSP000933
