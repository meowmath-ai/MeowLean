import JSP000930NegativeActualFinalKappaRealCover

open Cardinal

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes JSP000933.PreparedModel
  JSP000933.ForcingTransport JSP000930.Positive.Cohen

abbrev PlacementTableIndex :=
  GroundContinuumSuccIndex × (OmegaOneIndex × OmegaOneIndex)

variable {N : Type}

structure PlacementBook (N : Type) where
  trace : GroundContinuumSuccIndex → N
  traceSurjective : Function.Surjective trace
  mixed : ∀ c : GroundContinuumSuccIndex,
    MixedEnumeration OmegaOneIndex (ClosedKappaCut c) PreparedBA
  preparedReals : OmegaOneIndex → ℕ → PreparedBA
  preparedRealsCover : EnumeratesBooleanReals preparedReals

noncomputable def PlacementBook.row (F : PlacementBook N)
    (Q : ValuedPoset PreparedBA N) (i : PlacementTableIndex) : ℕ → TotalBA Q :=
  placementTableReal Q (F.mixed i.1) (fun j => F.trace j.val)
    i.2.1 (decodeCutCode i.2.1 (F.preparedReals i.2.2))

theorem exists_placementBook [Nonempty N] (hN : Cardinal.mk N ≤ GroundContinuumSucc) :
    Nonempty (PlacementBook N) := by
  classical
  obtain ⟨f,hf⟩ := exists_groundKappaTraceEnumeration_r477 N hN
  obtain ⟨u,hu⟩ := prepared_internalCH_enumeratesBooleanReals_r440
  exact ⟨⟨f,hf,fun c => Classical.choice
    (prepared_smallMixedTraceEnum_r471 (ClosedKappaCut c) (closedKappaCut_card c)),u,hu⟩⟩

theorem PlacementBook.rowsCover (F : PlacementBook N)
    (Q : ValuedPoset PreparedBA N) (hQ : ForcesRelativeCCC Q) (x : ℕ → TotalBA Q) :
    (⨆ i : PlacementTableIndex, realEqValue x (F.row Q i)) = ⊤ := by
  let f := F.trace
  let hf := F.traceSurjective
  let E₀ : MixedEnumeration GroundContinuumSuccIndex N PreparedBA := groundMixedEnumeration f hf
  let E := F.mixed
  let u := F.preparedReals
  have hu := F.preparedRealsCover
  let e := F.row Q
  change (⨆ i : PlacementTableIndex, realEqValue x (e i)) = ⊤
  let P (c : GroundContinuumSuccIndex) := actualKappaCut_boundedFamilies Q E₀ x c
  have hNat : Cardinal.mk ℕ < GroundContinuumSucc := by
    rw [Cardinal.mk_nat]
    exact Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _)
  have hTop : (⨆ c,baseEmbed Q (P c)) = ⊤ := by
    change (⨆ c,baseEmbed Q (actualKappaCut_boundedFamilies Q E₀ x c)) = ⊤
    rw [← baseEmbed_joins_r427,
      actualKappaCuts_cover_r476 Q hQ actual_prepared_boundsSmallKappa_r473 E₀ x hNat,
      baseEmbed_top_r427]
  apply top_unique
  rw [← hTop]
  apply iSup_le
  intro c
  let W := cutoffGreedyWeight Q f hf x c
  let y := weightedTraceReal Q (fun j : ClosedKappaCut c => f j.val) W
  have hY : baseEmbed Q (P c) ≤ realEqValue x y := by
    apply (le_realEqValue_iff_r126 _ _ _).mpr
    intro n
    change _ = baseEmbed Q (P c) ⊓ weightedTraceReal Q (fun j : ClosedKappaCut c => f j.val) W n
    rw [cutoffGreedyWeight_real]
    exact actualKappaCut_agrees_r476 Q E₀ x c (P c) le_rfl n
  have hE : (⨆ b : OmegaOneIndex,⨆ i : OmegaOneIndex,realEqValue y (e (c,b,i))) = ⊤ :=
    placedTraceReal_double_cover Q hQ prepared_boundsOmegaOne_r432 (E c)
      (fun j : ClosedKappaCut c => f j.val) W
      (cutoffGreedyWeight_valid Q f hf x c) (cutoffGreedyWeight_apart Q f hf x c) u hu
  rw [← inf_top_eq (baseEmbed Q (P c)),← hE,inf_iSup_eq]
  apply iSup_le
  intro b
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le (c,b,i)
  exact (le_inf (inf_le_left.trans hY) inf_le_right).trans (realEqValue_trans_r127 _ _ _)

end JSP000930.Negative
