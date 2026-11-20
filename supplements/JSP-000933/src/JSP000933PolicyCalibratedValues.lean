import JSP000933NativeOCAValues

namespace JSP000933
namespace CantorCodes

open BooleanCompletion FiniteSupport OpenGraphForcing

noncomputable abbrev ocaRules (P : OCAParameters) := iterationRules (ocaStagePolicy P)
abbrev ocaCondition (P : OCAParameters) := Condition (ocaRules P)
abbrev ocaB (P : OCAParameters) := RO (ocaCondition P)
abbrev ocaBefore (P : OCAParameters) (a : OmegaTwoIndex) := Before (ocaRules P) a
abbrev ocaOld (P : OCAParameters) (a : OmegaTwoIndex) := earlierValidated (ocaStagePolicy P) a

theorem ocaOldPersistent (P : OCAParameters) (a : OmegaTwoIndex) :
    HistoryPersistent (ocaOld P a) := earlierHistory_persistent_r131 (ocaStagePolicy P) a

noncomputable def ocaPrefixMap (P : OCAParameters) (a : OmegaTwoIndex) :
    CompleteValueMap (RO (GoodPrefix (ocaOld P a))) (RO (ocaBefore P a)) :=
  (orderIsoReduction (prefixOrderIso_r85 (ocaStagePolicy P) a)).completeValueMap

theorem ocaOldCCC (P : OCAParameters) (a : OmegaTwoIndex) :
    BooleanCCC (RO (GoodPrefix (ocaOld P a))) :=
  BooleanCCC_of_completeValueMap_r158 (ocaPrefixMap P a)
    (booleanCCC_of_conditionCCC_r66 (ocaPrefixCCC_r164 P a))

noncomputable def ocaTotalMap (P : OCAParameters) (a : OmegaTwoIndex) :
    CompleteValueMap (RO (GoodPrefix (ocaOld P a))) (ocaB P) :=
  (wholeReduction (R := ocaRules P) a).completeValueMap.comp (ocaPrefixMap P a)

theorem ocaTotalMap_basic_r167 (P : OCAParameters) (a : OmegaTwoIndex) (q : ocaBefore P a) :
    (ocaTotalMap P a).toFun (imageCondition ((prefixOrderIso_r85 (ocaStagePolicy P) a) q)) =
      imageCondition q.1 := by
  change (wholeReduction (R := ocaRules P) a).boolPullback
    ((orderIsoReduction (prefixOrderIso_r85 (ocaStagePolicy P) a)).boolPullback
      (imageCondition ((prefixOrderIso_r85 (ocaStagePolicy P) a) q))) = _
  rw [orderIsoReduction_basic_r122,OrderIso.symm_apply_apply,wholeReduction_basic_r100]

theorem exists_ocaSchedule_r167 (P : OCAParameters) :
    ∃ S : ReflectingNameSchedule (ocaRules P), S.code = P.names ∧
      S.stageEnumerate = actualHistoryEnum (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH :=
  exists_reflectingNameSchedule_fixed_r162 (ocaIterationCCC_r164 P) (ocaPrefixCCC_r164 P)
    P.names (actualHistoryEnum (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH)
    (actualHistoryEnum_surj_r161 (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH)

theorem historyGraphX_prefix_r167 (P : OCAParameters) (a : OmegaTwoIndex)
    (S : ReflectingNameSchedule (ocaRules P)) (hN : S.code = P.names)
    (hE : S.stageEnumerate = actualHistoryEnum (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH) :
    (fun i n => (ocaPrefixMap P a).toFun (historyGraphX P a (ocaOld P a)
      (ocaOldPersistent P a) (ocaOldCCC P a) i n)) = decodedX S a := by
  funext i n
  simp only [historyGraphX,decodedX,hN,hE]
  exact historyRealDecode_actual_r161 (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH
    P.names a i.1 (ocaOldPersistent P a) (ocaOldCCC P a) n

theorem historyGraphK_prefix_r167 (P : OCAParameters) (a j : OmegaTwoIndex)
    (S : ReflectingNameSchedule (ocaRules P)) (hN : S.code = P.names)
    (hE : S.stageEnumerate = actualHistoryEnum (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH) :
    (fun w => (ocaPrefixMap P a).toFun (historyGraphK P a (ocaOld P a)
      (ocaOldPersistent P a) (ocaOldCCC P a) j w)) = decodedK S a j := by
  funext w
  simp only [historyGraphK,decodedK,unpackColor,hN,hE]
  exact historyRealDecode_actual_r161 (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH
    P.names a j (ocaOldPersistent P a) (ocaOldCCC P a) (Encodable.encode w)

theorem historyGraphD_prefix_r167 (P : OCAParameters) (a : OmegaTwoIndex) :
    (fun i => (ocaPrefixMap P a).toFun (historyGraphD P a (ocaOld P a) i)) =
      decodedD (R := ocaRules P) P.encoder a (P.guess a) := by
  funext i
  exact historyDomain_actual_r160 (ocaStagePolicy P) P.encoder a (P.guess a) i.1

theorem ocaHistorySaturated_in_final_r167 (P : OCAParameters) (a : OmegaTwoIndex)
    (S : ReflectingNameSchedule (ocaRules P)) (hN : S.code = P.names)
    (hE : S.stageEnumerate = actualHistoryEnum (ocaStagePolicy P) (ocaPrefixCCC_r164 P) P.CH)
    (ha : a ∈ S.club) (D : (ℕ → ocaB P) → ocaB P) (hD : RealTestExt D)
    (hd : ∀ i : ↥(Set.Iio a), (wholeReduction (R := ocaRules P) a).boolPullback
      (decodedD (R := ocaRules P) P.encoder a (P.guess a) i) = D (S.enumerate i.1))
    (x : ℕ → RO (GoodPrefix (ocaOld P a))) :
    (ocaTotalMap P a).toFun (historySaturated P a (ocaOld P a) (ocaOldPersistent P a)
      (ocaOldCCC P a) x) ≤ D (fun n => (ocaTotalMap P a).toFun (x n)) := by
  unfold historySaturated
  rw [map_saturatedDomain_r127]
  apply saturatedDomain_le_extensional_r166 _ _ D hD
  intro i
  have hX := congrFun (historyGraphX_prefix_r167 P a S hN hE) i
  have hD' := congrFun (historyGraphD_prefix_r167 P a) i
  change (wholeReduction (R := ocaRules P) a).boolPullback
    ((ocaPrefixMap P a).toFun (historyGraphD P a (ocaOld P a) i)) ≤
    D (fun n => (wholeReduction (R := ocaRules P) a).boolPullback
      ((ocaPrefixMap P a).toFun (historyGraphX P a (ocaOld P a)
        (ocaOldPersistent P a) (ocaOldCCC P a) i n)))
  rw [hD',hd i]
  have h := S.localDecode_agrees a ha i.1 i.2
  change liftBitsToWhole a (decodedX S a i) = S.enumerate i.1 at h
  have hY : (fun n => (wholeReduction (R := ocaRules P) a).boolPullback
      ((ocaPrefixMap P a).toFun (historyGraphX P a (ocaOld P a)
        (ocaOldPersistent P a) (ocaOldCCC P a) i n))) = S.enumerate i.1 := by
    funext n
    rw [congrFun hX n]
    exact congrFun h n
  rw [hY] <;> exact le_rfl

end CantorCodes
end JSP000933
