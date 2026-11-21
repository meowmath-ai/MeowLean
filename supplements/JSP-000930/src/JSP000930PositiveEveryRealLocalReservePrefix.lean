import JSP000930PositiveGreedyRankLocalization
import Mathlib.Data.Finset.Image

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.CantorCodes
  JSP000933.RelativeOCA JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.ForcingTransport

noncomputable def reserveTraceScope (p : Trace WetzelCoordinate) : Finset OmegaOneIndex := by
  classical
  let raw := p.1.dom.image (fun x => Sum.elim (fun _ => none) some x.1)
  exact raw.filterMap id (by intro _ _ _ h a; exact h.trans a.symm)

theorem reserveTraceScope_bounded (p : Trace WetzelCoordinate) :
    ∃ c : OmegaOneIndex, ∀ i ∈ reserveTraceScope p, i < c := by
  obtain ⟨c,hc⟩ := OmegaOneIndex_countable_bounded_r61
    (reserveTraceScope p : Set OmegaOneIndex) (reserveTraceScope p).finite_toSet.countable
  exact ⟨c,hc⟩

noncomputable def reserveTraceRank (p : Trace WetzelCoordinate) : OmegaOneIndex :=
  Classical.choose (reserveTraceScope_bounded p)

theorem supported_reserve_of_rank {t : Trace WetzelCoordinate} {c : OmegaOneIndex}
    (h : reserveTraceRank t < c) : Supported t (reservePrefix c) := by
  rintro ⟨i,n⟩ hx
  cases i with
  | inl _ => exact True.intro
  | inr j =>
      change j < c
      apply (Classical.choose_spec (reserveTraceScope_bounded t) j ?_).trans h
      classical
      unfold reserveTraceScope
      exact (Finset.mem_filterMap id).2
        ⟨some j,Finset.mem_image.mpr ⟨(Sum.inr j,n),hx,rfl⟩,rfl⟩

theorem wetzel_real_local_reserve (x : ℕ → WetzelCohenBA) (p : WetzelCohenBA) (hp : p ≠ ⊥) :
    ∃ (c : OmegaOneIndex) (r : TotalCondition wetzelCohenPoset)
      (y : ℕ → TotalBA (valuedBlock PreparedBA (reservePrefix c))),
      imageCondition r ≤ p ∧
      imageCondition r ≤ realEqValue x
        (fun n => (markedBlockIntoFull (reservePrefix c)).toFun (y n)) := by
  classical
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 p hp
  obtain ⟨f,hf⟩ := wetzelTraces_enumerate
  let E : MixedEnumeration GroundContinuumSuccIndex (Trace WetzelCoordinate) PreparedBA :=
    groundMixedEnumeration f hf
  have hCCC : ForcesRelativeCCC wetzelCohenPoset :=
    cohen_forcesRelativeCCC prepared_boundsOmegaOne_r432
  obtain ⟨c,b,hb,hbt,hk⟩ := exists_local_greedy_rank_bound
    wetzelCohenPoset E hCCC prepared_boundsOmegaOne_r432 reserveTraceRank x t.mask t.nonzero
  let W (n : ℕ) := greedyTraceWeight wetzelCohenPoset E (x n)
  let J := {v : Trace WetzelCoordinate // reserveTraceRank v < c}
  let y (n : ℕ) : TotalBA (valuedBlock PreparedBA (reservePrefix c)) :=
    ⨆ k : GroundContinuumSuccIndex,⨆ v : J,
      traceRectangle (valuedBlock PreparedBA (reservePrefix c))
        ⟨v.val,supported_reserve_of_rank v.property⟩ (W n k v.val)
  let F := markedBlockIntoFull (B := PreparedBA) (reservePrefix c)
  have hy (n : ℕ) : F.toFun (y n) = ⨆ k : GroundContinuumSuccIndex,⨆ v : J,
      traceRectangle wetzelCohenPoset v.val (W n k v.val) := by
    simp only [y,F,(markedBlockIntoFull (B := PreparedBA) (reservePrefix c)).map_iSup,
      markedBlock_rectangle]
  let d := baseEmbed wetzelCohenPoset b
  have hEq (n : ℕ) : d ⊓ x n = d ⊓ F.toFun (y n) := by
    rw [hy n]
    apply le_antisymm
    · rw [← greedyTraceValue_eq_r466 wetzelCohenPoset E (x n)]
      change d ⊓ (⨆ k : GroundContinuumSuccIndex,⨆ v,traceRectangle wetzelCohenPoset v
        (W n k v)) ≤ _
      rw [inf_iSup_eq]
      apply iSup_le
      intro k
      rw [inf_iSup_eq]
      apply iSup_le
      intro v
      by_cases hv : reserveTraceRank v < c
      · exact le_inf inf_le_left (inf_le_right.trans (le_iSup_of_le k
          (le_iSup (fun w : J => traceRectangle wetzelCohenPoset w.val (W n k w.val)) ⟨v,hv⟩)))
      · have he := traceRectangle_disjoint_base_r467 wetzelCohenPoset v
          (hk n k v (le_of_not_gt hv))
        exact he.le.trans bot_le
    · apply inf_le_inf le_rfl
      apply iSup_le
      intro k
      apply iSup_le
      intro v
      exact (traceRectangle_accept_iff_r464 wetzelCohenPoset (x n) v.val _).mpr
        (greedyTraceWeight_accepted_r465 wetzelCohenPoset E (x n) k v.val)
  let r : TotalCondition wetzelCohenPoset := ⟨b,t.trace,hb,le_top⟩
  have hr : r ≤ t := (cohen_total_le_iff _ _).mpr ⟨hbt,le_rfl⟩
  refine ⟨c,r,y,(imageCondition_mono_r50 hr).trans ht,?_⟩
  exact (image_le_baseEmbed_r427 r b le_rfl).trans
    ((le_realEqValue_iff_r126 d _ _).mpr hEq)

end JSP000930.Positive.Cohen
