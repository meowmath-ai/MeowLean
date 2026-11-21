import JSP000930ActualWetzelSuccessorInvariant
import JSP000930NegativeRealPreparedRelativeDirectLimitCCC

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion
open scoped Cardinal

theorem checkedCut_contains_finset {a : GroundContinuumSuccIndex}
    (h0 : ∃ j,j<a) (hL : ∀ j,j<a → ∃ k,j<k ∧ k<a)
    (T : Finset GroundContinuumSuccIndex) (hT : ∀ j∈T,j<a) :
    ∃ k,k<a ∧ ∀ j∈T,j<k := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨j,hj⟩ := h0
    exact ⟨j,hj,by simp⟩
  | @insert j T hj ih =>
    obtain ⟨k,hk,hKT⟩ := ih (fun r hr => hT r (Finset.mem_insert_of_mem hr))
    obtain ⟨u,hju,hua⟩ := hL j (hT j (Finset.mem_insert_self _ _))
    refine ⟨max k u,max_lt hk hua,?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl|hr
    · exact hju.trans_le (le_max_right _ _)
    · exact (hKT r hr).trans_le (le_max_left _ _)

theorem wholeReduction_basic930 {A : Type} [LinearOrder A] {N : A → Type}
    {R : Rules N} {a : A} (p : Before R a) :
    (wholeReduction a).boolPullback (imageCondition p) = imageCondition p.val := by
  apply Heyting.Regular.coe_injective
  change (wholeReduction a).lowerPullback ((LowerSet.Iic p)ᶜᶜ) =
    ((LowerSet.Iic p.val)ᶜᶜ : LowerSet (Condition R))
  rw [RestrictionMap.lowerPullback_compl_r90,RestrictionMap.lowerPullback_compl_r90]
  have he : (wholeReduction a).lowerPullback (LowerSet.Iic p) = LowerSet.Iic p.val := by
    ext q
    change restrict q a ≤ p ↔ q ≤ p.val
    constructor
    · intro h
      change ∀ i,coordinateLE R.leAt i (cut q.trace a) p.val.trace at h
      change ∀ i,coordinateLE R.leAt i q.trace p.val.trace
      intro i v hv
      have hi : i<a := p.property i ⟨v,hv⟩
      obtain ⟨w,hw,hle⟩ := h i v hv
      exact ⟨w,(cut_apply_of_lt hi).symm.trans hw,by
        rw [cut_cut_of_le_r75 q.trace hi.le] at hle
        exact hle⟩
    · intro h
      have hm := restrict_mono_r75 h a
      rwa [restrict_fixed_r92 p] at hm
  rw [he]

abbrev NativeWetzelPrefixRO (a : GroundContinuumSuccIndex) :=
  RO (BasedBefore actualWetzelTail (wetzelWorkStage a))

noncomputable def nativePrefixComplete {a b : GroundContinuumSuccIndex} (h : a≤b) :
    CompleteValueMap (NativeWetzelPrefixRO a) (NativeWetzelPrefixRO b) :=
  (prefixReduction ((wetzelWorkStage_le_iff _ _).mpr h)).completeValueMap

noncomputable def nativePrefixBase (a : GroundContinuumSuccIndex) :
    CompleteValueMap PreparedBA (NativeWetzelPrefixRO a) :=
  basedPrefixEmbed actualWetzelTail (wetzel_bot_lt_work a)

noncomputable def nativePrefixIntoWhole (a : GroundContinuumSuccIndex) :
    CompleteValueMap (NativeWetzelPrefixRO a) (RO (BasedCondition actualWetzelTail)) :=
  (wholeReduction (wetzelWorkStage a)).completeValueMap

theorem nativePrefixComplete_comp {a b c : GroundContinuumSuccIndex} (hab : a≤b) (hbc : b≤c)
    (x : NativeWetzelPrefixRO a) :
    (nativePrefixComplete hbc).toFun ((nativePrefixComplete hab).toFun x) =
      (nativePrefixComplete (hab.trans hbc)).toFun x := by
  let ha := (wetzelWorkStage_le_iff _ _).mpr hab
  let hb := (wetzelWorkStage_le_iff _ _).mpr hbc
  change (prefixReduction hb).boolPullback ((prefixReduction ha).boolPullback x) =
    (prefixReduction (ha.trans hb)).boolPullback x
  apply Heyting.Regular.coe_injective
  ext p
  change restrict (restrict p.val (wetzelWorkStage b)).val (wetzelWorkStage a) ∈
      (x : LowerSet (BasedBefore actualWetzelTail (wetzelWorkStage a))) ↔ _
  rw [restrict_restrict_r92 p.val ha] <;> rfl

theorem nativeWetzelBoundFromWorkPart (p : BasedCondition actualWetzelTail) (k : GroundContinuumSuccIndex)
    (h : ∀ j, present p.trace (wetzelWorkStage j) → j<k) :
    ∀ i,present p.trace i → i<wetzelWorkStage k := by
  intro i hi
  cases i with
  | none => exact wetzel_bot_lt_work k
  | some i =>
    cases i with
    | bot => exact wetzelBulk_lt_work _
    | coe j => exact (wetzelWorkStage_lt_iff _ _).mpr (h j hi)

theorem nativeWetzelWorkSupportFinite (p : BasedCondition actualWetzelTail) :
    ({j | present p.trace (wetzelWorkStage j)} : Set GroundContinuumSuccIndex).Finite := by
  have hi : Function.Injective wetzelWorkStage := fun i j he => le_antisymm
    ((wetzelWorkStage_le_iff _ _).mp he.le) ((wetzelWorkStage_le_iff _ _).mp he.ge)
  exact p.finite.preimage hi.injOn

theorem nativeWetzelEarlierBasis {a : GroundContinuumSuccIndex}
    (h0 : ∃ j,j<a) (hL : ∀ j,j<a → ∃ k,j<k ∧ k<a)
    (p : BasedBefore actualWetzelTail (wetzelWorkStage a)) :
    ∃ (j : GroundContinuumSuccIndex) (hj : j<a) (r : BasedBefore actualWetzelTail (wetzelWorkStage j)),
      (nativePrefixComplete hj.le).toFun (imageCondition r) = imageCondition p := by
  let K := nativeWetzelWorkSupportFinite p.val
  obtain ⟨j,hj,hK⟩ := checkedCut_contains_finset h0 hL K.toFinset
    (fun k hk => (wetzelWorkStage_lt_iff _ _).mp (p.property _ (K.mem_toFinset.mp hk)))
  let r : BasedBefore actualWetzelTail (wetzelWorkStage j) :=
    ⟨p.val,nativeWetzelBoundFromWorkPart p.val j (fun k hk => hK k (K.mem_toFinset.mpr hk))⟩
  refine ⟨j,hj,r,?_⟩
  change (prefixReduction ((wetzelWorkStage_le_iff _ _).mpr hj.le)).boolPullback (imageCondition r) = _
  rw [prefixReduction_basic_r92] <;> rfl

theorem nativeWetzelFinalEarlierBasis (p : BasedCondition actualWetzelTail) :
    ∃ (j : GroundContinuumSuccIndex) (r : BasedBefore actualWetzelTail (wetzelWorkStage j)),
      (nativePrefixIntoWhole j).toFun (imageCondition r) = imageCondition p := by
  let K := nativeWetzelWorkSupportFinite p
  let J := (↥({j | present p.trace (wetzelWorkStage j)} : Set GroundContinuumSuccIndex))
  letI : Finite J := K.to_subtype
  have hSmall : Cardinal.mk J < GroundContinuumSucc :=
    (Cardinal.mk_le_aleph0 : Cardinal.mk J ≤ Cardinal.aleph0).trans_lt
      (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
  obtain ⟨j,hj⟩ := continuumSuccIndex_family_bounded_r399 Subtype.val hSmall
  let r : BasedBefore actualWetzelTail (wetzelWorkStage j) :=
    ⟨p,nativeWetzelBoundFromWorkPart p j (fun k hk => hj ⟨k,hk⟩)⟩
  exact ⟨j,r,wholeReduction_basic930 r⟩

end JSP000930.Negative
