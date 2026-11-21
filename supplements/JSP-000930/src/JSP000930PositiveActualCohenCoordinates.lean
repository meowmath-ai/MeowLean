import JSP000930PositiveFiniteTraceCardinality
import JSP000930PositiveActualCompleteBlockInclusion
import JSP000933PreparedKappaBounds
import JSP000933GroundKappaTraceEnum

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.RelativeOCA

abbrev WetzelRow := GroundContinuumSuccIndex ⊕ OmegaOneIndex
abbrev WetzelCoordinate := WetzelRow × ℕ

noncomputable abbrev wetzelCohenPoset := valuedCohen PreparedBA WetzelCoordinate

abbrev WetzelCohenBA := CohenBA PreparedBA WetzelCoordinate

def bulkPrefix (a : GroundContinuumSuccIndex) : Set WetzelCoordinate :=
  {x | Sum.elim (fun i => i < a) (fun _ => True) x.1}

def reservePrefix (a : OmegaOneIndex) : Set WetzelCoordinate :=
  {x | Sum.elim (fun _ => True) (fun i => i < a) x.1}

theorem finite_family_card_le (T : Type) {c : Cardinal}
    (hc : ℵ₀ ≤ c) (hT : Cardinal.mk T ≤ c) :
    Cardinal.mk (Finset T) ≤ c := by
  let e : T ↪ T ⊕ ℕ := ⟨Sum.inl,Sum.inl_injective⟩
  letI : Infinite (T ⊕ ℕ) := Infinite.of_injective Sum.inr Sum.inr_injective
  have he : Function.Injective (fun s : Finset T => s.map e) := Finset.map_injective e
  apply (Cardinal.mk_le_of_injective he).trans
  rw [Cardinal.mk_finset_of_infinite]
  simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.mk_nat]
  exact Cardinal.add_le_of_le hc hT hc

theorem cohen_trace_count_le (T : Type) {c : Cardinal}
    (hc : ℵ₀ ≤ c) (hT : Cardinal.mk T ≤ c) :
    Cardinal.mk (Trace T) ≤ c := by
  apply (trace_card_le_finset T).trans
  apply finite_family_card_le _ hc
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hc hT (Cardinal.mk_le_aleph0.trans hc)

theorem wetzelCoordinates_card :
    Cardinal.mk WetzelCoordinate ≤ GroundContinuumSucc := by
  have hc : (ℵ₀ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have hw : Cardinal.mk WetzelRow ≤ GroundContinuumSucc := by
    simp only [WetzelRow,Cardinal.mk_sum,Cardinal.lift_id,
      continuumSuccIndex_card_r406,mk_OmegaOneIndex_r61]
    exact Cardinal.add_le_of_le hc le_rfl
      (Cardinal.aleph_one_le_continuum.trans (Order.le_succ _))
  change Cardinal.mk (WetzelRow × ℕ) ≤ _
  simp only [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.mk_nat]
  exact Cardinal.mul_le_of_le hc hw hc

theorem wetzelTraces_card :
    Cardinal.mk (Trace WetzelCoordinate) ≤ GroundContinuumSucc :=
  cohen_trace_count_le _ (Cardinal.aleph0_le_continuum.trans (Order.le_succ _))
    wetzelCoordinates_card

instance : Nonempty (Trace WetzelCoordinate) := ⟨emptyTrace _⟩

theorem wetzelTraces_enumerate :
    ∃ f : GroundContinuumSuccIndex → Trace WetzelCoordinate, Function.Surjective f :=
  exists_groundKappaTraceEnumeration_r477 _ wetzelTraces_card

end JSP000930.Positive.Cohen
