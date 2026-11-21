import JSP000930PositiveFirstFamilyIndicesUnbounded

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.CantorCodes JSP000933.OpenGraphForcing
  JSP000933.PreparedModel JSP000933.RelativeOCA

theorem wetzel_unbounded_active_one_reserve
    (x : GroundContinuumSuccIndex → ℕ → WetzelCohenBA)
    (A : GroundContinuumSuccIndex → WetzelCohenBA)
    (p : WetzelCohenBA) (hp : p ≠ ⊥) (hA : p ≤ unboundedKappaValue A) :
    ∃ (c : OmegaOneIndex) (m : WetzelCohenBA), m ≠ ⊥ ∧ m ≤ p ∧
      m ≤ unboundedKappaValue (fun i => A i ⊓ availableAtReserve (x i) c) := by
  let W (c : OmegaOneIndex) (i : GroundContinuumSuccIndex) :=
    A i ⊓ availableAtReserve (x i) c
  have hCard : Cardinal.mk OmegaOneIndex < GroundContinuumSucc := by
    rw [mk_OmegaOneIndex_r61]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  have hRow : (fun i => ⨆ c,W c i) = A := by
    funext i
    change (⨆ c,A i ⊓ availableAtReserve (x i) c) = A i
    rw [← inf_iSup_eq,availableAtReserve_covers,inf_top_eq]
  have hCover : p ≤ ⨆ c,unboundedKappaValue (W c) := by
    rw [← unboundedKappaValue_smallPartition wetzelCohen_boundsKappa hCard W,hRow]
    exact hA
  exact exists_nonzero_below_choice_r135 p hp (fun c => unboundedKappaValue (W c)) hCover

end JSP000930.Positive.Cohen
