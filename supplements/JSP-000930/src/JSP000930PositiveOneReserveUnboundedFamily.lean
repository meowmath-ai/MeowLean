import JSP000930PositiveKappaSmallPartition

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.CantorCodes
  JSP000933.RelativeOCA JSP000933.PreparedModel JSP000933.OpenGraphForcing

noncomputable def availableAtReserve (x : ℕ → WetzelCohenBA) (c : OmegaOneIndex) :
    WetzelCohenBA :=
  ⨆ y : ℕ → TotalBA (valuedBlock PreparedBA (reservePrefix c)),
    realEqValue x (fun n => (markedBlockIntoFull (reservePrefix c)).toFun (y n))

theorem availableAtReserve_covers (x : ℕ → WetzelCohenBA) :
    (⨆ c,availableAtReserve x c) = ⊤ := by
  apply compl_eq_bot.mp
  apply value_eq_bot_of_dense_avoidance
  intro p hp
  obtain ⟨c,r,y,hr,he⟩ := wetzel_real_local_reserve x p hp
  have ha : imageCondition r ≤ ⨆ c,availableAtReserve x c :=
    he.trans (le_iSup_of_le c (le_iSup
      (fun z : ℕ → TotalBA (valuedBlock PreparedBA (reservePrefix c)) =>
        realEqValue x (fun n => (markedBlockIntoFull (reservePrefix c)).toFun (z n))) y))
  refine ⟨imageCondition r,imageCondition_ne_bot_r50 r,hr,?_⟩
  exact (disjoint_compl_right.mono_left ha).eq_bot

theorem kappa_above_nonempty (c : GroundContinuumSuccIndex) :
    Nonempty {i : GroundContinuumSuccIndex // c < i} := by
  have hShort : Cardinal.mk Unit < GroundContinuumSucc :=
    Cardinal.mk_le_aleph0.trans_lt (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
  obtain ⟨b,hb⟩ := continuumSuccIndex_family_bounded_r399
    (fun _ : Unit => c) hShort
  exact ⟨⟨b,hb ()⟩⟩

theorem unboundedKappaValue_const {B : Type} [CompleteBooleanAlgebra B] (p : B) :
    unboundedKappaValue (fun _ => p) = p := by
  have h (c : GroundContinuumSuccIndex) : aboveKappaValue (fun _ => p) c = p := by
    obtain ⟨i⟩ := kappa_above_nonempty c
    exact le_antisymm (iSup_le fun _ => le_rfl)
      (le_iSup (fun _ : {i : GroundContinuumSuccIndex // c < i} => p) i)
  apply le_antisymm
  · let c := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
    exact (iInf_le _ c).trans_eq (h c)
  · exact le_iInf (fun c => (h c).ge)

theorem wetzel_unbounded_one_reserve
    (x : GroundContinuumSuccIndex → ℕ → WetzelCohenBA)
    (p : WetzelCohenBA) (hp : p ≠ ⊥) :
    ∃ (c : OmegaOneIndex) (m : WetzelCohenBA), m ≠ ⊥ ∧ m ≤ p ∧
      m ≤ unboundedKappaValue (fun i => availableAtReserve (x i) c) := by
  let W (c : OmegaOneIndex) (i : GroundContinuumSuccIndex) := availableAtReserve (x i) c
  have hCard : Cardinal.mk OmegaOneIndex < GroundContinuumSucc := by
    rw [mk_OmegaOneIndex_r61]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  have hTop : (⨆ c,unboundedKappaValue (W c)) = ⊤ := by
    rw [← unboundedKappaValue_smallPartition wetzelCohen_boundsKappa hCard W]
    have hW : (fun i => ⨆ c,W c i) = fun _ => (⊤ : WetzelCohenBA) :=
      funext fun i => availableAtReserve_covers (x i)
    rw [hW,unboundedKappaValue_const]
  exact exists_nonzero_below_choice_r135 p hp (fun c => unboundedKappaValue (W c))
    (hTop.symm ▸ le_top)

end JSP000930.Positive.Cohen
