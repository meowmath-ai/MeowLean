import JSP000930PositiveEveryRealLocalBulkPrefix
import JSP000933RelativeSmallQuotientCH
import JSP000933PreparedSmallTraceEnum
import JSP000930PositiveReserveKernels

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.PreparedModel JSP000933.ForcingTransport JSP000933.CantorCodes
  JSP000933.OpenGraphForcing

theorem bulkPrefix_enumerates (a : GroundContinuumSuccIndex) :
    ∃ e : OmegaOneIndex → ℕ → TotalBA (valuedBlock PreparedBA (bulkPrefix a)),
      EnumeratesBooleanReals e := by
  obtain ⟨e,he⟩ := prepared_internalCH_enumeratesBooleanReals_r440
  obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471
    (BlockTrace (bulkPrefix a)) (bulkPrefixTrace_card a)
  exact relativeSmallCH_enumeratesBooleanReals_r469 (valuedBlock PreparedBA (bulkPrefix a))
    (block_forcesRelativeCCC (bulkPrefix a) prepared_boundsOmegaOne_r432)
    prepared_boundsOmegaOne_r432 E e he

theorem wetzelCohen_enumeration_pair :
    ∃ e : GroundContinuumSuccIndex × OmegaOneIndex → ℕ → WetzelCohenBA,
      ∀ x : ℕ → WetzelCohenBA, (⨆ i, realEqValue x (e i)) = ⊤ := by
  classical
  choose E hE using bulkPrefix_enumerates
  let F (a : GroundContinuumSuccIndex) := markedBlockIntoFull (B := PreparedBA) (bulkPrefix a)
  let e (i : GroundContinuumSuccIndex × OmegaOneIndex) (n : ℕ) : WetzelCohenBA :=
    (F i.1).toFun (E i.1 i.2 n)
  refine ⟨e,fun x => ?_⟩
  let g := ⨆ i, realEqValue x (e i)
  have hZ : gᶜ = ⊥ := by
    apply JSP000930.Positive.value_eq_bot_of_dense_avoidance
    intro p hp
    obtain ⟨a,r,y,hrp,hrEq⟩ := wetzel_real_local_bulk x p hp
    let d := imageCondition r
    let take (i : OmegaOneIndex) : WetzelCohenBA :=
      (F a).toFun (realEqValue y (E a i))
    have hT : (⨆ i,take i) = ⊤ := by
      change (⨆ i,(F a).toFun (realEqValue y (E a i))) = ⊤
      rw [← (F a).map_iSup,hE a y,(F a).map_top]
    have hd : d ≤ g := by
      rw [← inf_top_eq d,← hT,inf_iSup_eq]
      apply iSup_le
      intro i
      apply le_iSup_of_le (a,i)
      apply (le_inf (inf_le_left.trans hrEq) ?_).trans (realEqValue_trans_r127 _ _ _)
      have hi := map_realEqValue_r126 (F a) y (E a i)
      exact inf_le_right.trans hi.le
    exact ⟨d,imageCondition_ne_bot_r50 r,hrp,
      le_bot_iff.mp (disjoint_iff_inf_le.mp (disjoint_compl_right.mono_left hd))⟩
  exact compl_eq_bot.mp hZ

theorem kappaTimesOmegaOne_reindex :
    Nonempty (GroundContinuumSuccIndex ≃ GroundContinuumSuccIndex × OmegaOneIndex) := by
  apply Cardinal.eq.mp
  simp only [Cardinal.mk_prod,Cardinal.lift_id,continuumSuccIndex_card_r406,mk_OmegaOneIndex_r61]
  have hK : (ℵ₀ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have h1 : (ℵ₁ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)
  exact (Cardinal.mul_eq_left hK h1
    (ne_of_gt (Cardinal.aleph0_pos.trans_le Cardinal.isRegular_aleph_one.1))).symm

theorem wetzelCohen_kappa_realCover :
    ∃ e : GroundContinuumSuccIndex → ℕ → WetzelCohenBA,
      ∀ x : ℕ → WetzelCohenBA, (⨆ i, realEqValue x (e i)) = ⊤ := by
  obtain ⟨f,hf⟩ := wetzelCohen_enumeration_pair
  obtain ⟨u⟩ := kappaTimesOmegaOne_reindex
  refine ⟨fun i => f (u i),fun x => ?_⟩
  rw [generic_iSup_equiv_r413 u (fun i => realEqValue x (f i))]
  exact hf x

end JSP000930.Positive.Cohen
