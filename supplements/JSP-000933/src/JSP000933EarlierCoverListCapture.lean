import JSP000933ActualCoverFromEarlierPrefix

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

variable (tail : BasedTailPolicy PreparedStage PreparedBA CliqueLabel)

noncomputable def typedToTypedLater (a d : PreparedStage) (had : a≤d) :
    CompleteValueMap (PreStageAlgebra tail (a := a)) (PreStageAlgebra tail (a := d)) :=
  composeCompleteValueMaps (typedToLater tail a d had)
    (completeValueMapOfIso (typedPrefixROIso tail d).symm)

theorem typedToTypedLater_whole_coherent (a d : PreparedStage) (had : a≤d)
    (x : PreStageAlgebra tail (a := a)) :
    (typedToWhole tail d).toFun ((typedToTypedLater tail a d had).toFun x)=
      (typedToWhole tail a).toFun x := by
  change (wholeReduction (R := iterationRules (basedPolicy tail)) d).boolPullback
    (typedPrefixROIso tail d ((typedPrefixROIso tail d).symm
      ((prefixReduction (R := iterationRules (basedPolicy tail)) had).boolPullback
        (typedPrefixROIso tail a x)))) = _
  rw [OrderIso.apply_symm_apply,wholeReduction_coherent_r110] <;> rfl

noncomputable def scheduledRealList
    (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (a : GroundContinuumSuccIndex) :
    OmegaOneIndex→ℕ→PreparedPrefixBA (scheduledTail decode) a :=
  Classical.choose (scheduledPreparedPrefix_CH decode a)

theorem scheduledRealList_enumerates (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (a : GroundContinuumSuccIndex) : EnumeratesBooleanReals (scheduledRealList decode a) :=
  Classical.choose_spec (scheduledPreparedPrefix_CH decode a)

noncomputable def coverList (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (a : GroundContinuumSuccIndex) (i : OmegaOneIndex) :
    CoverCode (PreparedPrefixBA (scheduledTail decode) a) :=
  decodeCoverReal (scheduledRealList decode a i)

noncomputable def coverListInWhole (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (a : GroundContinuumSuccIndex) (i : OmegaOneIndex) :
    CoverCode (RO (BasedCondition (scheduledTail decode))) :=
  fun n w => (typedToWhole (scheduledTail decode) (a : PreparedStage)).toFun (coverList decode a i n w)

theorem capture_cover_from_list (decode : ActualScheduleDecoder PreparedStage PreparedBA)
    (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d)
    (c : CoverCode (PreparedPrefixBA (scheduledTail decode) d))
    (p : PreparedPrefixBA (scheduledTail decode) d) (hp : p≠⊥) :
    ∃ (a : GroundContinuumSuccIndex) (i : OmegaOneIndex)
      (s : PreparedPrefixBA (scheduledTail decode) d), a<d ∧ s≤p ∧ s≠⊥ ∧
      ∀ n w,(typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun s⊓
        (typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun (c n w) =
        (typedToWhole (scheduledTail decode) (d : PreparedStage)).toFun s⊓
        coverListInWhole decode a i n w := by
  obtain ⟨a,r,c',ha,hr,hr0,hLocal⟩ := earlyCover_at_cofOmegaOne decode d hd c p hp
  let tail := scheduledTail decode
  let a' : PreparedStage := (a : PreparedStage)
  let d' : PreparedStage := (d : PreparedStage)
  have had : a'≤d' := WithBot.coe_le_coe.mpr ha.le
  let E := typedToTypedLater tail a' d' had
  let F := typedToWhole tail d'
  let x := encodeCoverReal c'
  let w (i : OmegaOneIndex) := realEqValue x (scheduledRealList decode a i)
  have hW : (⨆ i,E.toFun (w i))=⊤ := by
    rw [←E.map_iSup]
    change E.toFun (⨆ i,realEqValue x (scheduledRealList decode a i))=⊤
    rw [scheduledRealList_enumerates decode a x,E.map_top]
  have hPos : ∃ i, r⊓E.toFun (w i)≠⊥ := by
    by_contra hn
    apply hr0
    calc
      r = r⊓(⨆ i,E.toFun (w i)) := by rw [hW,inf_top_eq]
      _ = ⨆ i,r⊓E.toFun (w i) := inf_iSup_eq _ _
      _ = ⊥ := by
        apply le_bot_iff.mp
        apply iSup_le
        intro i
        by_contra hi
        exact hn ⟨i,fun he => hi he.le⟩
  obtain ⟨i,hi⟩ := hPos
  let s := r⊓E.toFun (w i)
  refine ⟨a,i,s,ha,inf_le_left.trans hr,hi,?_⟩
  intro n v
  have hs : F.toFun s≤F.toFun r := F.monotone inf_le_left
  have hOld := congrArg (fun z => F.toFun s⊓z) (hLocal n v)
  rw [←inf_assoc,←inf_assoc,inf_eq_left.mpr hs] at hOld
  apply hOld.trans
  have hEq := (le_realEqValue_iff_r126 _ _ _).mp (show w i≤w i from le_rfl) (Encodable.encode (n,v))
  have he : x (Encodable.encode (n,v))=c' n v :=
    congrFun (congrFun (decode_encodeCoverReal c') n) v
  rw [he] at hEq
  have hInner := congrArg E.toFun hEq
  simp only [E.map_inf] at hInner
  have hs' : s≤E.toFun (w i) := inf_le_right
  have hInner' := congrArg (fun z => s⊓z) hInner
  rw [←inf_assoc,←inf_assoc,inf_eq_left.mpr hs'] at hInner'
  have hResult := congrArg F.toFun hInner'
  simp only [F.map_inf] at hResult
  change (typedToWhole tail d').toFun s ⊓
      (typedToWhole tail d').toFun ((typedToTypedLater tail a' d' had).toFun (c' n v)) =
    (typedToWhole tail d').toFun s ⊓ (typedToWhole tail d').toFun
      ((typedToTypedLater tail a' d' had).toFun (scheduledRealList decode a i (Encodable.encode (n,v)))) at hResult
  rw [typedToTypedLater_whole_coherent,typedToTypedLater_whole_coherent] at hResult
  exact hResult

end ForcingTransport
end JSP000933
