import JSP000930ActualWetzelMasterLabels

open scoped Cardinal

namespace JSP000930.Negative

open Cardinal JSP000930.Positive.Cohen JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing

abbrev WetzelStageIndex := WithBot (WithBot GroundContinuumSuccIndex)

def wetzelBulkStage : WetzelStageIndex := ((⊥ : WithBot GroundContinuumSuccIndex) : WetzelStageIndex)

def wetzelWorkStage (a : GroundContinuumSuccIndex) : WetzelStageIndex :=
  ((a : WithBot GroundContinuumSuccIndex) : WetzelStageIndex)

theorem card_option_le930 {T : Type} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) (hT : #T ≤ κ) :
    #(Option T) ≤ κ := by
  let code : Option T → Unit ⊕ T
    | none => Sum.inl ()
    | some n => Sum.inr n
  have hc : Function.Injective code := by
    rintro (_|a) (_|b) h <;> cases h <;> rfl
  apply (Cardinal.mk_le_of_injective hc).trans
  simp only [Cardinal.mk_sum,Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ (Cardinal.mk_le_aleph0.trans hκ) hT

theorem certifiedStageLabel_card_le {T : Type} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) (hT : #T ≤ κ) :
    #(CertifiedStageLabel T) ≤ κ := by
  let code : CertifiedStageLabel T → Option (T × List T × List (T × T))
    | .weak => none
    | .list a l o => some (a,l,o)
  have hc : Function.Injective code := by
    intro x y h
    cases x <;> cases y <;> cases h <;> rfl
  have hTT : #(T×T) ≤ κ := by
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact Cardinal.mul_le_of_le hκ hT hT
  have hL₁ : #(List T) ≤ κ := (Cardinal.mk_list_le_max _).trans (max_le hκ hT)
  have hL₂ : #(List (T×T)) ≤ κ := (Cardinal.mk_list_le_max _).trans (max_le hκ hTT)
  apply (Cardinal.mk_le_of_injective hc).trans
  apply card_option_le930 hκ
  change #(T × (List T × List (T×T))) ≤ κ
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hκ hT (Cardinal.mul_le_of_le hκ hL₁ hL₂)

theorem wetzelMasterLabels_card : #WetzelMasterLabel ≤ GroundContinuumSucc := by
  let κ := GroundContinuumSucc
  have hk : (ℵ₀ : Cardinal) ≤ κ := Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  let code : WetzelMasterLabel → Unit ⊕
      (Trace WetzelCoordinate ⊕ (Option (SymbolicTrace GroundContinuumSuccIndex) × Trace WorkCohenCoordinate))
    | .zero => Sum.inl ()
    | .bulk t => Sum.inr (Sum.inl t)
    | .work p t => Sum.inr (Sum.inr (p,t))
  have hc : Function.Injective code := by
    intro x y h
    cases x <;> cases y <;> cases h <;> rfl
  have hJ : #GroundContinuumSuccIndex ≤ κ := by
    exact continuumSuccIndex_card_r406.le
  have hO : #OmegaOneIndex ≤ κ := by
    rw [mk_OmegaOneIndex_r61]
    exact Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)
  have hN : #ℕ ≤ κ := Cardinal.mk_le_aleph0.trans hk
  have hNB : #ℕ * #Bool ≤ κ :=
    Cardinal.mul_le_of_le hk hN (Cardinal.mk_le_aleph0.trans hk)
  have hCoord : #WorkCohenCoordinate ≤ κ := by
    change #((OmegaOneIndex × (ℕ × Bool)) × ℕ) ≤ κ
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact Cardinal.mul_le_of_le hk (Cardinal.mul_le_of_le hk hO hNB) hN
  have hL : #(Option (SymbolicTrace GroundContinuumSuccIndex)) ≤ κ :=
    card_option_le930 hk (symbolicTrace_card_le κ hk hJ)
  have hR : #(Trace WorkCohenCoordinate) ≤ κ := cohen_trace_count_le _ hk hCoord
  apply (Cardinal.mk_le_of_injective hc).trans
  simp only [Cardinal.mk_sum,Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.add_le_of_le hk (Cardinal.mk_le_aleph0.trans hk)
    (Cardinal.add_le_of_le hk wetzelTraces_card (Cardinal.mul_le_of_le hk hL hR))

theorem wetzelCertifiedLabels_card : #WetzelCertifiedLabel ≤ GroundContinuumSucc :=
  certifiedStageLabel_card_le (Cardinal.aleph0_le_continuum.trans (Order.le_succ _))
    wetzelMasterLabels_card

theorem wetzelStageIndex_card : #WetzelStageIndex ≤ GroundContinuumSucc := by
  change #(Option (Option GroundContinuumSuccIndex)) ≤ GroundContinuumSucc
  have hk : (ℵ₀ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  exact card_option_le930 hk (card_option_le930 hk continuumSuccIndex_card_r406.le)

end JSP000930.Negative
