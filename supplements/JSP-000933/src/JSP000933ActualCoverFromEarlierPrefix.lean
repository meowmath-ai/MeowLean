import JSP000933PreparedPrefixCHRealCodes
import JSP000933ActualEarlyRealAtCofOmegaOne
import JSP000933NameScheduleCoherence

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

variable (tail : BasedTailPolicy PreparedStage PreparedBA CliqueLabel)

noncomputable def relativePrefixToWhole (a : PreparedStage) (ha : (⊥ : PreparedStage)<a) :
    CompleteValueMap (TotalBA (prefixTailPresentation tail ha).quotient) (RO (BasedCondition tail)) :=
  composeCompleteValueMaps (completeValueMapOfIso (prefixTailPresentation tail ha).denseMap.pullIso)
    (wholeReduction (R := iterationRules (basedPolicy tail)) a).completeValueMap

theorem typedToRelativePrefix_base (a d : PreparedStage) (ha : (⊥ : PreparedStage)<a) (had : a≤d)
    (v : PreparedBA) :
    (typedToRelativePrefix tail a d ha had).toFun
      (typedPreparedBase (earlierValidated (basedPolicy tail) a) v) =
      baseEmbed (prefixTailPresentation tail (ha.trans_le had)).quotient v := by
  let S := prefixTailPresentation tail (ha.trans_le had)
  apply S.denseMap.pullIso.injective
  change S.denseMap.pullIso (S.denseMap.pullIso.symm
    ((prefixReduction (R := iterationRules (basedPolicy tail)) had).boolPullback
      (typedPrefixROIso tail a (typedPreparedBase (earlierValidated (basedPolicy tail) a) v))))=_
  rw [S.denseMap.pullIso.apply_symm_apply,typedPreparedBase_image tail a ha,
    basedPrefix_base_commutes tail ha had,S.quotient_base_coherent]

theorem typedToRelativePrefix_trace (a d : PreparedStage) (ha : (⊥ : PreparedStage)<a) (had : a≤d)
    (n : PrefixTail d CliqueLabel) (hn : ∀ i,present n.trace i → i<a) :
    ∃ y : PreStageAlgebra tail (a := a), (typedToRelativePrefix tail a d ha had).toFun y =
      traceValue (prefixTailPresentation tail (ha.trans_le had)).quotient n := by
  let S := prefixTailPresentation tail (ha.trans_le had)
  let n' : PrefixTail a CliqueLabel := ⟨n.trace,n.finite,hn⟩
  have he : includeRawTail (fun _ h => h.trans_le had) n'=n := RawTail.extTrace rfl
  refine ⟨typedRawTailJoin (earlierValidated (basedPolicy tail) a)
    (includeRawTail (fun _ _ => trivial) n'),S.denseMap.pullIso.injective ?_⟩
  change S.denseMap.pullIso (S.denseMap.pullIso.symm
    ((prefixReduction (R := iterationRules (basedPolicy tail)) had).boolPullback
      (typedPrefixROIso tail a (typedRawTailJoin (earlierValidated (basedPolicy tail) a)
        (includeRawTail (fun _ _ => trivial) n')))))=_
  rw [S.denseMap.pullIso.apply_symm_apply,typedRawTailJoin_image tail a ha,
    earlier_to_later_traceValue tail ha had,he]

theorem typedToRelativePrefix_whole_coherent (a d : PreparedStage)
    (ha : (⊥ : PreparedStage)<a) (had : a≤d) (x : PreStageAlgebra tail (a := a)) :
    (relativePrefixToWhole tail d (ha.trans_le had)).toFun
      ((typedToRelativePrefix tail a d ha had).toFun x)=(typedToWhole tail a).toFun x := by
  let S := prefixTailPresentation tail (ha.trans_le had)
  change (wholeReduction (R := iterationRules (basedPolicy tail)) d).boolPullback
    (S.denseMap.pullIso (S.denseMap.pullIso.symm
      ((prefixReduction (R := iterationRules (basedPolicy tail)) had).boolPullback
        (typedPrefixROIso tail a x)))) = _
  rw [S.denseMap.pullIso.apply_symm_apply,wholeReduction_coherent_r110] <;> rfl

def carryStageBit {a d : PreparedStage} (h : a=d)
    (x : PreStageAlgebra tail (a := a)) : PreStageAlgebra tail (a := d) := h ▸ x

theorem typedToWhole_carryStageBit {a d : PreparedStage} (h : a=d)
    (x : PreStageAlgebra tail (a := a)) :
    (typedToWhole tail d).toFun (carryStageBit tail h x)=(typedToWhole tail a).toFun x := by
  subst d
  rfl

theorem earlyCover_at_cofOmegaOne (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d)
    (c : CoverCode (PreparedPrefixBA (scheduledTail decode) d))
    (p : PreparedPrefixBA (scheduledTail decode) d) (hp : p≠⊥) :
    ∃ (a : GroundContinuumSuccIndex) (s : PreparedPrefixBA (scheduledTail decode) d)
      (c' : CoverCode (PreparedPrefixBA (scheduledTail decode) a)), a<d ∧ s≤p ∧ s≠⊥ ∧
      ∀ n w,(typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun s⊓
        (typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun (c n w) =
        (typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun s⊓
        (typedToWhole (scheduledTail decode) (a : PreparedStage)).toFun (c' n w) := by
  let tail := scheduledTail decode
  let d' : PreparedStage := (d : PreparedStage)
  let hd' : (⊥ : PreparedStage)<d' := WithBot.bot_lt_coe d
  let S := prefixTailPresentation tail hd'
  let Q := S.quotient
  let F := (typedPrefixROIso tail d').trans S.denseMap.pullIso.symm
  have hQ : ForcesRelativeCCC Q :=
    S.quotient_relativeCCC (scheduledTail_prefix_projectedCCC decode prepared_boundsOmegaOne_r432 _ hd')
  letI : Nonempty (PrefixTail d' CliqueLabel) := ⟨⊤⟩
  obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471 (PrefixTail d' CliqueLabel) (prefixRawTail_card_r491 d)
  let A (a : GroundContinuumSuccIndex) := PreparedPrefixBA tail (min a d)
  let aCast (a : GroundContinuumSuccIndex) : PreparedStage := (min a d : GroundContinuumSuccIndex)
  have h₀ (a : GroundContinuumSuccIndex) : (⊥ : PreparedStage)<aCast a := WithBot.bot_lt_coe _
  have h₁ (a : GroundContinuumSuccIndex) : aCast a≤d' := WithBot.coe_le_coe.mpr (min_le_right a d)
  let M (a : GroundContinuumSuccIndex) : CompleteValueMap (A a) (TotalBA Q) :=
    typedToRelativePrefix tail (aCast a) d' (h₀ a) (h₁ a)
  let base (a : GroundContinuumSuccIndex) (b : PreparedBA) : A a :=
    typedPreparedBase (earlierValidated (basedPolicy tail) (aCast a)) b
  have hB (a : GroundContinuumSuccIndex) (b : PreparedBA) :
      (M a).toFun (base a b)=baseEmbed Q b :=
    typedToRelativePrefix_base tail (aCast a) d' (h₀ a) (h₁ a) b
  have hT (a : GroundContinuumSuccIndex) (n : PrefixTail d' CliqueLabel)
      (hn : ∀ k∈physicalRawTailScope_r491 n,k<a) :
      ∃ y : A a, (M a).toFun y=traceValue Q n := by
    apply typedToRelativePrefix_trace tail (aCast a) d' (h₀ a) (h₁ a) n
    exact (physicalRawTailScope_lt_iff_r491 n (min a d)).mp (fun k hk =>
      lt_min (hn k hk) (prefixRawTail_physicalScope_r491 d n k hk))
  have hp' : F p≠⊥ := fun h => hp (F.injective (h.trans F.map_bot.symm))
  obtain ⟨a,r,x,ha,hr,hMatch⟩ := earlyReal_at_cofOmegaOne_r489 Q hQ
    prepared_boundsOmegaOne_r432 E d hd physicalRawTailScope_r491
    (prefixRawTail_physicalScope_r491 d) A M base hB hT
    (F ∘ encodeCoverReal c) (F p) hp'
  have he : min a d=a := min_eq_left ha.le
  let s := F.symm (imageCondition r)
  have hs : s≤p := F.le_iff_le.mp (by simpa only [s,F.apply_symm_apply] using hr)
  have hs0 : s≠⊥ := by
    intro h
    apply imageCondition_ne_bot_r50 r
    have h' := congrArg F h
    simpa only [s,F.apply_symm_apply,F.map_bot] using h'
  have hX := (le_realEqValue_iff_r126 _ _ _).mp hMatch
  have hCast : aCast a=(a : PreparedStage) := congrArg (fun x : GroundContinuumSuccIndex => (x : PreparedStage)) he
  let X : ℕ→PreparedPrefixBA tail a := fun n => carryStageBit tail hCast (x n)
  refine ⟨a,s,decodeCoverReal X,ha,hs,hs0,?_⟩
  intro n w
  have hh := congrArg (relativePrefixToWhole tail d' hd').toFun (hX (Encodable.encode (n,w)))
  simp only [(relativePrefixToWhole tail d' hd').map_inf] at hh
  have hId (v : PreparedPrefixBA tail d) :
      (relativePrefixToWhole tail d' hd').toFun (F v) = (typedToWhole tail d').toFun v := by
    change (wholeReduction (R := iterationRules (basedPolicy tail)) d').boolPullback
      (S.denseMap.pullIso (S.denseMap.pullIso.symm (typedPrefixROIso tail d' v)))=_
    rw [S.denseMap.pullIso.apply_symm_apply] <;> rfl
  have hR : (relativePrefixToWhole tail d' hd').toFun (imageCondition r) =
      (typedToWhole tail d').toFun s := by rw [←hId s]; simp [s]
  rw [hR] at hh
  change _ ⊓ (relativePrefixToWhole tail d' hd').toFun (F (encodeCoverReal c (Encodable.encode (n,w)))) =
    _ ⊓ (relativePrefixToWhole tail d' hd').toFun ((M a).toFun (x (Encodable.encode (n,w)))) at hh
  rw [hId,typedToRelativePrefix_whole_coherent tail (aCast a) d' (h₀ a) (h₁ a)] at hh
  have hDec : encodeCoverReal c (Encodable.encode (n,w))=c n w :=
    congrFun (congrFun (decode_encodeCoverReal c) n) w
  rw [hDec] at hh
  change (typedToWhole tail d').toFun s ⊓ _ =
    (typedToWhole tail d').toFun s⊓(typedToWhole tail (a : PreparedStage)).toFun
      (X (Encodable.encode (n,w)))
  simpa only [X,typedToWhole_carryStageBit] using hh

end ForcingTransport
end JSP000933
