import JSP000933ActualWorstMeetAndEmpty

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem snapshotPropValue_inf_r373 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (j : ℕ) (P Q : ActualBlockSnapshot j → Prop) :
    snapshotPropValue T j P⊓snapshotPropValue T j Q ≤ snapshotPropValue T j (fun d => P d∧Q d) := by
  classical
  unfold snapshotPropValue
  rw [iSup_inf_iSup]
  apply iSup_le
  rintro ⟨D,E⟩
  by_cases he : D=E
  · subst E
    apply le_iSup_of_le D
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    rw [crisp_and_r190]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  · have hD := (actualBlockSnapshotPartition T j).separate D E he
    exact ((inf_le_inf inf_le_left inf_le_left).trans_eq hD.eq_bot).trans bot_le

theorem blockInputMeet_empty_of_disjoint_r373 {k : ℕ} {H : ActualStageHistory (k+2)}
    (x y : BlockInput H) (h : Disjoint x.val y.val) : blockInputMeet x y=emptyBlockInput H := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hm
  exact Finset.disjoint_left.mp h hx hy

theorem groundDisjointActOverlap_budget_r373 {j : ℕ} (D : ActualBlockSnapshot j) (k : ℕ)
    (x y : BlockInput D.history) (hD : Disjoint x.val y.val)
    (hM : GroundAllBudgets true (2*k) (snapshotActMeetDefect D x y))
    (hE : GroundAllBudgets true (2*k) (D.act (emptyBlockInput D.history))) :
    GroundAllBudgets true k (D.act x∩D.act y) := by
  intro n
  apply GroundBudgetHolds.of_diff_cover_r232 true k n _ (hM n) (hE n)
  intro m hm
  have hm' : m∈D.act x∩D.act y := hm.1
  have he := blockInputMeet_empty_of_disjoint_r373 x y hD
  by_cases h : m∈D.act (emptyBlockInput D.history)
  · exact Or.inr ⟨h,by simp⟩
  · left
    refine ⟨?_,by simp⟩
    unfold snapshotActMeetDefect
    rw [he]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hm',h⟩))

theorem actualDisjointOverlaps_eventuallyBudget_r373 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (k : ℕ) (hk : k≠0) :
    p≤eventuallyStageValue (fun j => snapshotPropValue T j
      (fun D => ∀ x y : BlockInput D.history, Disjoint x.val y.val → GroundAllBudgets true k (D.act x∩D.act y))) := by
  have hk' : 2*k≠0 := by omega
  have hA := actualAllMeetDefects_eventuallyBudget_r372 F T hC hL (2*k) hk'
  have hB := actualEmptyImage_eventuallyBudget_r372 F T hL (2*k) hk'
  apply (le_inf hA hB).trans
  apply (eventuallyStageValue_join_r372 _ _).trans
  apply eventuallyStageValue_mono_r372
  intro j
  apply (snapshotPropValue_inf_r373 T j _ _).trans
  exact snapshotPropValue_mono_r372 T j (fun D h x y hD =>
    groundDisjointActOverlap_budget_r373 D k x y hD (h.1 x y) h.2)

end SetLanguage
end JSP000933
