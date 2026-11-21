import JSP000930NegativeMixedCanonicalTrialCover

open Cardinal

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000930.Positive
  JSP000930.BooleanAnalysis

theorem placementTrialIndex_card : Cardinal.mk PlacementTrialIndex ≤ GroundContinuumSucc := by
  have hK : (ℵ₀ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have h1 : (ℵ₁ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)
  have hT : Cardinal.mk PlacementTableIndex ≤ GroundContinuumSucc := by
    simp only [PlacementTableIndex,Cardinal.mk_prod,Cardinal.lift_id,
      continuumSuccIndex_card_r406,mk_OmegaOneIndex_r61]
    exact Cardinal.mul_le_of_le hK le_rfl (Cardinal.mul_le_of_le hK h1 h1)
  simp only [PlacementTrialIndex,Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hK hT hT

def PlacementBook.TrialReady {N : Type} (F : PlacementBook N)
    (scope : N → Finset GroundContinuumSuccIndex) (a : GroundContinuumSuccIndex)
    (i : PlacementTrialIndex) : Prop :=
  (∀ t : ClosedKappaCut i.1.1,TraceBelow scope a (F.trace t.val)) ∧
  (∀ t : ClosedKappaCut i.2.1,TraceBelow scope a (F.trace t.val))

theorem PlacementBook.trialReady_mono {N : Type} (F : PlacementBook N)
    {scope : N → Finset GroundContinuumSuccIndex} {a b : GroundContinuumSuccIndex}
    {i : PlacementTrialIndex} (h : F.TrialReady scope a i) (hab : a ≤ b) :
    F.TrialReady scope b i :=
  ⟨fun t d hd => (h.1 t d hd).trans_le hab,fun t d hd => (h.2 t d hd).trans_le hab⟩

theorem PlacementBook.exists_readyTrialSchedule {N : Type} (F : PlacementBook N)
    (scope : N → Finset GroundContinuumSuccIndex) :
    ∃ pick : GroundContinuumSuccIndex → PlacementTrialIndex,
      ∀ (i : PlacementTrialIndex) (bound : GroundContinuumSuccIndex),
        ∃ j,bound < j ∧ pick j = i ∧ F.TrialReady scope j i := by
  letI : Nonempty GroundContinuumSuccIndex := ⟨continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos⟩
  letI : Nonempty OmegaOneIndex := Cardinal.mk_ne_zero_iff.mp (by
    rw [mk_OmegaOneIndex_r61]
    exact (Cardinal.aleph_pos _).ne')
  obtain ⟨f,hf⟩ := exists_groundKappaTraceEnumeration_r477 PlacementTrialIndex placementTrialIndex_card
  obtain ⟨g,hg⟩ := exists_cofinalSiteRequestSchedule
  refine ⟨f ∘ g,?_⟩
  intro i bound
  obtain ⟨a,ha,hb⟩ := F.two_initialScopes scope i.1 i.2
  obtain ⟨tag,htag⟩ := hf i
  obtain ⟨j,hj,hgj⟩ := hg tag (max bound a)
  exact ⟨j,(le_max_left _ _).trans_lt hj,
    (congrArg f hgj).trans htag,
    F.trialReady_mono ⟨ha,hb⟩ ((le_max_right _ _).trans hj.le)⟩

theorem PlacementPrefixSystem.readyTrial_at
    {N : Type} {Q : ValuedPoset PreparedBA N}
    (P : PlacementPrefixSystem Q)
    (F : PlacementBook N) (i : PlacementTrialIndex) (a : GroundContinuumSuccIndex)
    (h : F.TrialReady P.scope a i) :
    ∃ z : ComplexBits (TotalBA (P.poset a)),
      z.CutOn (trialValidity z) ∧
      mapComplexBits (P.into a) z = F.trial Q i ∧
      (P.into a).toFun (trialValidity z) = trialValidity (F.trial Q i) := by
  let x := P.localRow F i.1 a h.1
  let y := P.localRow F i.2 a h.2
  let z := decodeTrial x y
  have he := decodeTrial_commutes (P.into a) x y _ _
    (P.localRow_commutes F i.1 a h.1) (P.localRow_commutes F i.2 a h.2)
  exact ⟨z,(le_trialValidity_iff _ _).mp le_rfl,he,
    (trialValidity_map (P.into a) z).trans (congrArg trialValidity he)⟩

end JSP000930.Negative
