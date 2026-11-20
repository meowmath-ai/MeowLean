import JSP000933ActualTypedProbeCoherence
import JSP000933ActualRawTailCardinality
import JSP000933RelativeSmallQuotientCH
import JSP000933PreparedSmallTraceEnum
import JSP000933CountableChoiceProfiles

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

theorem preparedStage_noMax : NoMaxOrder PreparedStage := by
  constructor
  intro a
  cases a with
  | none =>
    let i := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
    exact ⟨(i : PreparedStage),WithBot.bot_lt_coe i⟩
  | some i =>
    let α := continuumSuccOrdinal i+1
    have h := (Cardinal.isSuccLimit_ord groundContinuumSucc_regular_r392.1).add_one_lt
      (continuumSuccOrdinal_lt_r392 i)
    refine ⟨(continuumSuccIndexOf α h : PreparedStage),WithBot.coe_lt_coe.mpr ?_⟩
    rw [continuumSuccIndex_lt_iff_r399,continuumSuccIndexOf_ordinal_r399]
    exact Order.lt_add_one_iff.mpr le_rfl

theorem preparedStage_successor (a : GroundContinuumSuccIndex) :
    ∃ b : PreparedStage,∀ i : PreparedStage,i<b ↔ i≤(a : PreparedStage) := by
  let α := continuumSuccOrdinal a+1
  have h := (Cardinal.isSuccLimit_ord groundContinuumSucc_regular_r392.1).add_one_lt
    (continuumSuccOrdinal_lt_r392 a)
  let b := continuumSuccIndexOf α h
  refine ⟨(b : PreparedStage),fun i => ?_⟩
  cases i with
  | none => exact ⟨fun _ => bot_le,fun _ => WithBot.bot_lt_coe b⟩
  | some i =>
    change ((i : PreparedStage)<(b : PreparedStage)) ↔ (i : PreparedStage)≤(a : PreparedStage)
    rw [WithBot.coe_lt_coe,WithBot.coe_le_coe,continuumSuccIndex_lt_iff_r399,
      continuumSuccIndex_le_iff_r399]
    change continuumSuccOrdinal i < continuumSuccOrdinal (continuumSuccIndexOf α h) ↔ _
    rw [continuumSuccIndexOf_ordinal_r399]
    exact Order.lt_add_one_iff

variable (tail : BasedTailPolicy PreparedStage PreparedBA CliqueLabel)

abbrev PreparedPrefixBA (a : GroundContinuumSuccIndex) :=
  PreStageAlgebra tail (a := (a : PreparedStage))

noncomputable def typedToLater (a d : PreparedStage) (had : a≤d) :
    CompleteValueMap (PreStageAlgebra tail (a := a)) (RO (BasedBefore tail d)) :=
  composeCompleteValueMaps (completeValueMapOfIso (typedPrefixROIso tail a))
    (prefixReduction (R := iterationRules (basedPolicy tail)) had).completeValueMap

noncomputable def typedToRelativePrefix (a d : PreparedStage) (ha : (⊥ : PreparedStage)<a) (had : a≤d) :
    CompleteValueMap (PreStageAlgebra tail (a := a))
      (TotalBA (prefixTailPresentation tail (ha.trans_le had)).quotient) :=
  composeCompleteValueMaps (typedToLater tail a d had)
    (completeValueMapOfIso (prefixTailPresentation tail (ha.trans_le had)).denseMap.pullIso.symm)

theorem booleanRealEnum_push_iso {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
    (F : B≃o C) (e : OmegaOneIndex→ℕ→B) (he : EnumeratesBooleanReals e) :
    EnumeratesBooleanReals (fun i n => F (e i n)) := by
  intro x
  let M := completeValueMapOfIso F
  have h := congrArg M.toFun (he (F.symm ∘ x))
  rw [M.map_iSup,M.map_top] at h
  simp only [map_realEqValue_r126] at h
  change (⨆ i,realEqValue (fun n => F (F.symm (x n))) (fun n => F (e i n)))=⊤ at h
  simpa only [F.apply_symm_apply] using h

theorem prepared_boundsOmegaOne_r432 : BoundsCountableOmegaOneNames PreparedBA := by
  intro V
  let m : PreparedBA := ⨅ n : ℕ, ⨆ i : OmegaOneIndex, V n i
  let w : PreparedBA := ⨆ b : OmegaOneIndex, ⨅ n : ℕ, ⨆ i : ↥(Set.Iio b), V n i.val
  change m ≤ w
  by_contra h
  have hNonzero : m ⊓ wᶜ ≠ ⊥ := fun hEq =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr hEq.le))
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hNonzero
  obtain ⟨q,f,hqp,hV⟩ := exists_allChoiceProfiles_r411 preparedProduct_countablyClosed_r401 p V
    (fun n => hp.trans (inf_le_left.trans (iInf_le (fun l => ⨆ i, V l i) n)))
  obtain ⟨b,hb⟩ := OmegaOneIndex_countable_bounded_r61 (Set.range f) (Set.countable_range f)
  have hQ : imageCondition q ≤ w := by
    apply le_iSup_of_le b
    apply le_iInf
    intro n
    exact (hV n).trans (le_iSup (fun i : ↥(Set.Iio b) => V n i.val) ⟨f n,hb _ ⟨n,rfl⟩⟩)
  exact imageCondition_ne_bot_r50 q
    (disjoint_compl_right.out _ hQ ((imageCondition_mono_r50 hqp).trans (hp.trans inf_le_right)))

theorem scheduledPreparedPrefix_CH (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (a : GroundContinuumSuccIndex) :
    ∃ e : OmegaOneIndex→ℕ→PreparedPrefixBA (scheduledTail decode) a,EnumeratesBooleanReals e := by
  let tail := scheduledTail decode
  let a' : PreparedStage := (a : PreparedStage)
  have ha : (⊥ : PreparedStage)<a' := WithBot.bot_lt_coe a
  let S := prefixTailPresentation tail ha
  have hCCC : ForcesRelativeCCC S.quotient :=
    S.quotient_relativeCCC (scheduledTail_prefix_projectedCCC decode prepared_boundsOmegaOne_r432 _ ha)
  letI : Nonempty (PrefixTail a' CliqueLabel) := ⟨⊤⟩
  obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471 (PrefixTail a' CliqueLabel) (prefixRawTail_card_r491 a)
  obtain ⟨e,he⟩ := prepared_internalCH_enumeratesBooleanReals_r440
  obtain ⟨e',he'⟩ := relativeSmallCH_enumeratesBooleanReals_r469 S.quotient hCCC
    prepared_boundsOmegaOne_r432 E e he
  let F := S.denseMap.pullIso.trans (typedPrefixROIso tail a').symm
  exact ⟨fun i n => F (e' i n),booleanRealEnum_push_iso F e' he'⟩

def decodeCoverReal {B : Type} (x : ℕ→B) : CoverCode B :=
  fun n w => x (Encodable.encode (n,w))

def encodeCoverReal {B : Type} [Bot B] (c : CoverCode B) : ℕ→B :=
  fun k => match Encodable.decode (α := ℕ×Word) k with
  | none => ⊥
  | some (n,w) => c n w

theorem decode_encodeCoverReal {B : Type} [Bot B] (c : CoverCode B) :
    decodeCoverReal (encodeCoverReal c)=c := by
  funext n w
  simp [decodeCoverReal,encodeCoverReal,Encodable.encodek]

end ForcingTransport
end JSP000933
