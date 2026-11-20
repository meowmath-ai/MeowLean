import JSP000933PreparedActivatedStageClique
import JSP000933ActualReflectedProbeBook

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

theorem preparedRawTailEnumeration_exists :
    ∃ f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel, Function.Surjective f := by
  classical
  let N := WholeTail PreparedStage CliqueLabel
  have hN : Cardinal.mk N≤Cardinal.mk GroundContinuumSuccIndex :=
    wholeRawTail_card_r491.trans_eq continuumSuccIndex_card_r406.symm
  obtain ⟨ι⟩ := (Cardinal.le_def _ _).mp hN
  let f (i : GroundContinuumSuccIndex) : N := if h : ∃ n,ι n=i then Classical.choose h else ⊤
  refine ⟨f,fun n => ?_⟩
  have hn : ∃ n',ι n'=ι n := ⟨n,rfl⟩
  refine ⟨ι n,ι.injective ?_⟩
  simpa only [f,dite_eq_left hn] using Classical.choose_spec hn

noncomputable def preparedRawTailEnumeration := Classical.choose preparedRawTailEnumeration_exists

theorem preparedRawTailEnumeration_surj : Function.Surjective preparedRawTailEnumeration :=
  Classical.choose_spec preparedRawTailEnumeration_exists

noncomputable def actualPreparedOcaDecoder : ActualScheduleDecoder PreparedStage PreparedBA :=
  preparedDecoder preparedProbeBook preparedRawTailEnumeration

noncomputable def actualPreparedOcaTail : BasedTailPolicy PreparedStage PreparedBA CliqueLabel :=
  scheduledTail actualPreparedOcaDecoder

abbrev ActualPreparedOcaCondition := BasedCondition actualPreparedOcaTail
abbrev ActualPreparedOcaBA := RO ActualPreparedOcaCondition

instance : Nonempty ActualPreparedOcaCondition := ⟨basedEmpty actualPreparedOcaTail⟩

set_option maxHeartbeats 1000000 in
theorem actualPreparedOca_graphDichotomy
    (D : (ℕ→ActualPreparedOcaBA)→ActualPreparedOcaBA) (hD : RealTestExt D)
    (K : Word×Word→ActualPreparedOcaBA) :
    irreflexiveGraphValue D K⊓symmetricGraphValue D K ≤
      closedCoverExistsValue D K⊔weightedCliqueExistsValue D K := by
  classical
  letI : NoMaxOrder PreparedStage := preparedStage_noMax
  by_contra hn
  let p : ActualPreparedOcaBA := (irreflexiveGraphValue D K⊓symmetricGraphValue D K)⊓
    (closedCoverExistsValue D K⊔weightedCliqueExistsValue D K)ᶜ
  have hp : p≠⊥ := fun h =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr h.le))
  have hNo (c : CoverCode ActualPreparedOcaBA) : p≤(goodCoverValue id D K c)ᶜ :=
    inf_le_right.trans (compl_le_compl ((le_iSup (fun c => goodCoverValue id D K c) c).trans le_sup_left))
  have hNotClique : p≤(weightedCliqueExistsValue D K)ᶜ :=
    inf_le_right.trans (compl_le_compl le_sup_right)
  have hIrr (x : ℕ→ActualPreparedOcaBA) : p⊓D x≤(colorValue K x x)ᶜ := by
    apply (le_materialImp_iff_r126 _ _ _).mp
    exact inf_le_left.trans (inf_le_left.trans (iInf_le _ x))
  have hSym (x y : ℕ→ActualPreparedOcaBA) :
      (p⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x := by
    rw [inf_assoc]
    apply (le_materialImp_iff_r126 _ _ _).mp
    exact inf_le_left.trans (inf_le_right.trans ((iInf_le _ x).trans (iInf_le _ y)))
  let f := preparedRawTailEnumeration
  let decode := actualPreparedOcaDecoder
  let tail := actualPreparedOcaTail
  have hExist (a : GroundContinuumSuccIndex) (j : OmegaOneIndex) :
      ∃ x y : ℕ→ActualPreparedOcaBA,
        p≤twoPointCoverFailure D K (coverListInWhole decode a j) x y :=
    exists_twoPointCoverFailure_maximum D hD K _ p (hNo _)
  choose x y hxy using hExist
  let W : ProbeWitnessPlan ActualPreparedOcaBA := fun a j b =>
    let z := if b then y a j else x a j
    (z,D z)
  let X := probeWitnessBits W
  have hFail (a : GroundContinuumSuccIndex) (j : OmegaOneIndex) :
      p≤twoPointCoverFailure D K (coverListInWhole decode a j)
        (X (preparedProbeWitnessIndex a j false)) (X (preparedProbeWitnessIndex a j true)) := by
    simpa [X,probeWitnessBits_at_r496,W] using hxy a j
  let S := wholeTailPresentation tail
  let Q := S.quotient
  have hQ : ForcesRelativeCCC Q :=
    S.quotient_relativeCCC (scheduledTail_whole_projectedCCC decode prepared_boundsOmegaOne_r432)
  let F := S.denseMap.pullIso
  let pQ := F.symm p
  have hpQ : pQ≠⊥ := by
    intro h
    apply hp
    simpa only [pQ,F.apply_symm_apply,F.map_bot] using congrArg F h
  let start := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  obtain ⟨R⟩ := exists_actual_reflectedBook_r497 Q hQ f preparedRawTailEnumeration_surj
    physicalRawTailScope_r491 start (fun i n => F.symm (X i n))
    (fun i => F.symm (D (X i))) (F.symm ∘ K) pQ pQ hpQ
  have hBase : F (baseEmbed Q R.baseMark) = (basedMaskRealization tail).embed R.baseMark :=
    S.quotient_base_coherent R.baseMark
  have hEq {u v : TotalBA Q} (h : preparedProbeEq Q R.baseMark u v) :
      (basedMaskRealization tail).embed R.baseMark⊓F u =
      (basedMaskRealization tail).embed R.baseMark⊓F v := by
    have hh := congrArg F h
    change F (baseEmbed Q R.baseMark⊓u)=F (baseEmbed Q R.baseMark⊓v) at hh
    rw [F.map_inf,F.map_inf,hBase] at hh
    exact hh
  have hPos : (basedMaskRealization tail).embed R.baseMark⊓p≠⊥ := by
    intro hz
    have h : F (imageCondition R.master) ≤ F (pQ ⊓ baseEmbed Q R.baseMark) :=
      F.monotone R.masterBelow
    have hpEq : F pQ = p := F.apply_symm_apply p
    rw [F.map_inf,hpEq,hBase,inf_comm p] at h
    have hh : F (imageCondition R.master) ≤ (basedMaskRealization tail).embed R.baseMark ⊓ p := h
    have hbot := F.injective ((le_bot_iff.mp (hh.trans_eq hz)).trans F.map_bot.symm)
    exact imageCondition_ne_bot_r50 R.master hbot
  obtain ⟨hBad,hK,_,_,_⟩ := earlyPreparedProbes_below_r495 R.closedRows start R.aboveStart
  have hSched (a : GroundContinuumSuccIndex) (ha : a<R.d) (j : OmegaOneIndex) (b : Bool) :
      preparedProbeWitnessIndex a j b<R.d ∧
        preparedProbeBook.completePoint R.d (preparedProbeWitnessIndex a j b) := by
    obtain ⟨_,_,_,_,h⟩ := earlyPreparedProbes_below_r495 R.closedRows a ha
    obtain ⟨h1,h2,h3⟩ := h j b
    exact ⟨h1,h3,h2⟩
  let M : DecodedBookMatches preparedProbeBook f R.d D K p X :=
    ⟨R.baseMark,hPos,hBad,hK,fun j hj =>
      (physicalRawTailScope_lt_iff_r491 (f j) R.d).mp (R.scopeBelow j hj),
      fun i hi n _ => (congrArg (fun z => (basedMaskRealization tail).embed R.baseMark ⊓ z)
        (F.apply_symm_apply (X i n))).symm.trans (hEq (R.bitMatches i hi n)),
      fun i hi _ => (congrArg (fun z => (basedMaskRealization tail).embed R.baseMark ⊓ z)
        (F.apply_symm_apply (D (X i)))).symm.trans (hEq (R.memberMatches i hi)),
      fun w => (congrArg (fun z => (basedMaskRealization tail).embed R.baseMark ⊓ z)
        (F.apply_symm_apply (K w))).symm.trans (hEq (R.graphMatches w)),
      (congrArg (fun z => (basedMaskRealization tail).embed R.baseMark ⊓ z)
        (F.apply_symm_apply p)).symm.trans (hEq R.badMatches)⟩
  obtain ⟨q,hq,hqp,hAct,hDom,hColor⟩ := preparedDecoder_activates_on_witness_book
    preparedProbeBook f R.d R.cofOmegaOne preparedProbeWitnessIndex hSched D hD K p X M hIrr hSym hFail
  obtain ⟨z,hz,hzq,hClique⟩ := preparedDecoder_locally_gives_finalClique
    preparedProbeBook f R.d q hq hAct D K hDom hColor
  exact hz (disjoint_compl_right.out _ hClique (hzq.trans (hqp.trans hNotClique)))

theorem actualPreparedOca_nativeOCA_top : nativeOCAValue ActualPreparedOcaBA=⊤ := by
  apply top_unique
  apply le_iInf
  intro D
  apply le_iInf
  intro K
  have h := actualPreparedOca_graphDichotomy D.val D.property K
  calc
    (⊤ : ActualPreparedOcaBA) =
        (irreflexiveGraphValue D.val K⊓symmetricGraphValue D.val K)ᶜ ⊔
          (irreflexiveGraphValue D.val K⊓symmetricGraphValue D.val K) := compl_sup_eq_top.symm
    _ ≤ _ := sup_le_sup_left h _

end ForcingTransport
end JSP000933
