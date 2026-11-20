import JSP000933PolicyCalibratedValues

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion OpenGraphForcing

structure ActivatedAt (P : OCAParameters) (D : (ℕ → ocaB P) → ocaB P)
    (K : Word × Word → ocaB P) (p : ocaCondition P) (a : OmegaTwoIndex) where
  choice : StageChoice P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a)
  admission : ocaStagePolicy P a (ocaOld P a) =
    StageChoice.admission P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a) choice
  condition_agrees : (ocaTotalMap P a).toFun (imageCondition choice.mark.cond) = imageCondition p
  code_agrees : ∀ w, (ocaTotalMap P a).toFun (historyGraphK P a (ocaOld P a)
    (ocaOldPersistent P a) (ocaOldCCC P a) choice.mark.color w) = K w
  domain_included : ∀ x, (ocaTotalMap P a).toFun (historySaturated P a (ocaOld P a)
    (ocaOldPersistent P a) (ocaOldCCC P a) x) ≤ D (fun n => (ocaTotalMap P a).toFun (x n))

theorem exists_matching_activation_r168 (P : OCAParameters) (hDia : DiamondAtOmegaOne P.guess)
    (D : (ℕ → ocaB P) → ocaB P) (hD : RealTestExt D) (K : Word × Word → ocaB P)
    (p : ocaCondition P)
    (hNo : ∀ c : CoverCode (ocaB P), imageCondition p ≤ (goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ x, imageCondition p ⊓ D x ≤ (colorValue K x x)ᶜ)
    (hSym : ∀ x y, (imageCondition p ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x) :
    ∃ a : OmegaTwoIndex, Nonempty (ActivatedAt P D K p a) := by
  classical
  obtain ⟨S,hN,hE⟩ := exists_ocaSchedule_r167 P
  have hSmall (a : OmegaTwoIndex) : Cardinal.mk (ocaBefore P a) ≤ ℵ₁ :=
    (Cardinal.mk_congr (prefixOrderIso_r85 (ocaStagePolicy P) a).toEquiv).le.trans
      (mk_goodCliquePrefix_le_r160 a (ocaOld P a))
  have hNoEnum (c : CoverCode (ocaB P)) :
      imageCondition p ≤ (goodCoverValue S.enumerate (fun i => D (S.enumerate i)) K c)ᶜ := by
    rw [indexed_goodCoverValue_eq_of_surj_r166 S.enumerate S.onto]
    exact hNo c
  obtain ⟨a,j,q,hCof,ha,hj,hq,hColorLt,hColorMem,hCondLt,hCondMem,hColorUnique,hCondUnique,
    hDExact,hKExact,hNoStage⟩ :=
    exists_guessedNoCoverStage_strong_r165 (ocaIterationCCC_r164 P) hSmall
      S P.encoder P.guess hDia (fun i => D (S.enumerate i)) K p hNoEnum
  let e := prefixOrderIso_r85 (ocaStagePolicy P) a
  let m : StageMark a (ocaOld P a) := ⟨j,e q⟩
  let L := ocaPrefixMap P a
  let F := ocaTotalMap P a
  let histD := historySaturated P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a)
  let histK := historyGraphK P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a)
  have hXLocal := historyGraphX_prefix_r167 P a S hN hE
  have hDLocal := historyGraphD_prefix_r167 P a
  have hKLocal := historyGraphK_prefix_r167 P a j S hN hE
  have hDTotal (x : ℕ → RO (GoodPrefix (ocaOld P a))) :
      F.toFun (histD x) ≤ D (fun n => F.toFun (x n)) :=
    ocaHistorySaturated_in_final_r167 P a S hN hE ha D hD hDExact x
  have hKTotal (w : Word × Word) : F.toFun (histK j w) = K w :=
    (congrArg ((wholeReduction (R := ocaRules P) a).boolPullback) (congrFun hKLocal w)).trans (hKExact w)
  have hpTotal : F.toFun (imageCondition m.cond) = imageCondition p :=
    (ocaTotalMap_basic_r167 P a q).trans (congrArg imageCondition hq)
  have hpLocal : L.toFun (imageCondition m.cond) = imageCondition q := by
    change (orderIsoReduction e).boolPullback (imageCondition (e q)) = _
    rw [orderIsoReduction_basic_r122,OrderIso.symm_apply_apply]
  have hTrace : goodTraceCode P.encoder m.cond = P.encoder.conditionCode q.1 :=
    goodTraceCode_actual_r159 (ocaStagePolicy P) P.encoder q
  have hMark : StageMark.eligible P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a) m := by
    refine ⟨hj,hColorLt,hColorMem,?_,?_,?_,?_,?_⟩
    · rw [hTrace]; exact hCondLt
    · rw [hTrace]; exact hCondMem
    · intro c
      apply L.reflect_le_r93
      rw [L.map_compl,map_goodCoverValue_r166,hXLocal,hDLocal,hKLocal,hpLocal]
      exact hNoStage (fun n w => L.toFun (c n w))
    · intro x
      apply F.reflect_le_r93
      simp only [F.map_inf,F.map_compl,map_colorValue_r105,hpTotal]
      change imageCondition p ⊓ F.toFun (histD x) ≤
        (colorValue (fun w => F.toFun (histK j w)) (fun n => F.toFun (x n)) (fun n => F.toFun (x n)))ᶜ
      rw [funext hKTotal]
      exact (inf_le_inf_left _ (hDTotal x)).trans (hIrr _)
    · intro x y
      apply F.reflect_le_r93
      simp only [F.map_inf,map_colorValue_r105,hpTotal]
      change (imageCondition p ⊓ (F.toFun (histD x) ⊓ F.toFun (histD y))) ⊓
        colorValue (fun w => F.toFun (histK j w)) (fun n => F.toFun (x n)) (fun n => F.toFun (y n)) ≤ _
      rw [funext hKTotal]
      exact (inf_le_inf_right _ (inf_le_inf_left _ (inf_le_inf (hDTotal x) (hDTotal y)))).trans (hSym _ _)
  have hSome := exists_stageChoice_r163 P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a) m hMark
  let s := Classical.choice hSome
  have hS := s.eligible
  have hColor : s.mark.color = j := hColorUnique _ hS.2.1 hS.2.2.1
  let oldCond := e.symm s.mark.cond
  have hT : goodTraceCode P.encoder s.mark.cond = P.encoder.conditionCode oldCond.1 := by
    simpa only [oldCond,e,OrderIso.apply_symm_apply] using
      goodTraceCode_actual_r159 (ocaStagePolicy P) P.encoder oldCond
  have hO : oldCond = q := hCondUnique oldCond
    (by rw [← hT]; exact hS.2.2.2.1)
    (by rw [← hT]; exact hS.2.2.2.2.1)
  have hCond : s.mark.cond = m.cond := by
    simpa only [m,oldCond,OrderIso.apply_symm_apply] using congrArg e hO
  refine ⟨a,⟨s,ocaStagePolicy_active_r164 P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a) hSome,
    ?_,?_,hDTotal⟩⟩
  · rw [hCond]; exact hpTotal
  · intro w
    rw [hColor]
    exact hKTotal w

end CantorCodes
end JSP000933
