import JSP000933ActivatesGenuineReflectedBook

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

def transportQuotientMap {B C N : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
    {Q Q' : ValuedPoset B N} (h : Q=Q') (F : CompleteValueMap (TotalBA Q) C) :
    CompleteValueMap (TotalBA Q') C := h ▸ F

theorem transportQuotientMap_base {B C N : Type} [CompleteBooleanAlgebra B]
    [CompleteBooleanAlgebra C] {Q Q' : ValuedPoset B N} (h : Q=Q')
    (F : CompleteValueMap (TotalBA Q) C) (b : B) :
    (transportQuotientMap h F).toFun (baseEmbed Q' b)=F.toFun (baseEmbed Q b) := by
  subst Q'
  rfl

theorem preparedDecoder_locally_gives_finalClique
    (book : ProbeBook) (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (a : GroundContinuumSuccIndex)
    (q : PreparedPrefixBA (scheduledTail (preparedDecoder book f)) a) (hq : q≠⊥)
    (hqM : q≤(actualDecodedGraph book f a).mark)
    (D : (ℕ→RO (BasedCondition (scheduledTail (preparedDecoder book f)))) →
      RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (K : Word×Word→RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (hD : ∀ x,(typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun q⊓
        (typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun
          ((actualDecodedGraph book f a).D x) ≤
          D ((typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun ∘ x))
    (hK : ∀ w,(typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun q⊓
        (typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun
          ((actualDecodedGraph book f a).K w) =
          (typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun q⊓K w) :
    ∃ z : RO (BasedCondition (scheduledTail (preparedDecoder book f))), z≠⊥ ∧
      z≤(typedToWhole (scheduledTail (preparedDecoder book f)) (a : PreparedStage)).toFun q ∧
      z≤weightedCliqueExistsValue D K := by
  classical
  letI : NoMaxOrder PreparedStage := preparedStage_noMax
  let decode := preparedDecoder book f
  let tail := scheduledTail decode
  let c : PreparedStage := (a : PreparedStage)
  have hc : (⊥ : PreparedStage)<c := WithBot.bot_lt_coe a
  let H := actualDecodedGraph book f a
  let E := typedToWhole tail c
  let M := prefixMaskRealization tail hc
  let L := basedMaskRealization tail
  have hPrev :=
    projectedCCC_preserves_boundsOmegaOne M.project M.embed M.project_gc M.embed_mono
      (fun _ => M.embed_joins) M.embed_top M.embed_compl prepared_boundsOmegaOne_r432
      (scheduledTail_prefix_projectedCCC decode prepared_boundsOmegaOne_r432 c hc)
  have hΩ : BoundsCountableOmegaOneNames (PreparedPrefixBA tail a) :=
    rowBounds_ofIso (typedPrefixROIso tail c).symm hPrev
  have hFinal := projectedCCC_preserves_boundsOmegaOne L.project L.embed L.project_gc L.embed_mono
    (fun _ => L.embed_joins) L.embed_top L.embed_compl prepared_boundsOmegaOne_r432
    (scheduledTail_whole_projectedCCC decode prepared_boundsOmegaOne_r432)
  have hExt : RealTestExt H.D := by
    change RealTestExt (saturatedDomain _ _)
    exact saturatedDomain_ext_r142 _ _
  obtain ⟨e,he⟩ := scheduledPreparedPrefix_CH decode a
  have hSel : Nonempty (RelativeCliqueStageData H.D H.K H.mark) :=
    exists_actualRelativeCliqueStage_r463 hΩ H.D hExt H.K H.mark
      (activationValue_noCover _ _ _) (activationValue_irreflexive _ _ _)
      (activationValue_symmetric _ _ _) e he
  let S := Classical.choice hSel
  obtain ⟨b,succ⟩ := preparedStage_successor a
  have hcb : c≤b := ((succ c).mpr le_rfl).le
  let G : CompleteValueMap (RO (BasedBefore tail b)) (RO (BasedCondition tail)) :=
    (wholeReduction (R := iterationRules (basedPolicy tail)) b).completeValueMap
  let J : CompleteValueMap (TotalBA H.quotient) (RO (BasedBefore tail b)) :=
    completeValueMapOfIso
      (markedSuccessorPullIso tail (ne_of_gt hc) H.iterandValues_monotone H.iterandValues_top succ)
  let F0 := composeCompleteValueMaps J G
  let Fe := transportQuotientMap (H.quotient_active hSel) F0
  have hCo (x : PreparedPrefixBA tail a) :
      Fe.toFun (baseEmbed S.iterand x)=E.toFun x := by
    change (transportQuotientMap (H.quotient_active hSel) F0).toFun (baseEmbed S.iterand x) = E.toFun x
    refine (transportQuotientMap_base (H.quotient_active hSel) F0 x).trans ?_
    change (wholeReduction (R := iterationRules (basedPolicy tail)) b).boolPullback
      ((markedSuccessorPullIso tail (ne_of_gt hc) H.iterandValues_monotone
        H.iterandValues_top succ) (baseEmbed H.quotient x))=_
    refine (congrArg ((wholeReduction (R := iterationRules (basedPolicy tail)) b).boolPullback)
      (markedSuccessor_base_commutes tail (ne_of_gt hc) H.iterandValues_monotone H.iterandValues_top succ x)).trans ?_
    rw [wholeReduction_coherent_r110,←orderIso_dense_pull_reduction] <;> rfl
  exact relativeStage_clique_on_localized_mark S E Fe hCo hFinal q hq hqM D K hD hK

end ForcingTransport
end JSP000933
