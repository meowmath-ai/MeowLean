import JSP000933ActualSourceGraftPrefix

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def crispStageWindow {n : ℕ} (H : ActualStageHistory n) (k m : ℕ) : B :=
  crispTruth B (m∈groundStageWindow H k)

theorem stageGraft_apply_r360 {q : B} {L : (ℕ → B) → ℕ → B}
    {k : ℕ} {d : ActualGroundStage} (hG : q≤actualStageGraftValue L k d)
    (x u v : ℕ → B) (n : ℕ) (hn : d.out≤n)
    (hMid : q≤actualMiddleMatch x d.left d.right d.pad) :
    q≤nameErrorBudget true (dyadicGapDen k) n
      (L (actualPrefixPatch d.left u x)) (L (actualPrefixPatch d.left v x)) := by
  have hx := (hG.trans (iInf_le _ x)).trans (iInf_le _ u)
  have hy := (hx.trans (iInf_le _ v)).trans (iInf_le _ ⟨n,hn⟩)
  exact (le_inf le_rfl hMid).trans ((le_materialImp_iff_r126 _ _ _).mp hy)

theorem stagePrefix_apply_r360 {q : B} {L : (ℕ → B) → ℕ → B} {d : ActualGroundStage}
    (hP : q≤actualStagePrefixValue L d) {x y : ℕ → B}
    (hXY : q≤actualPrefixMatch x y d.right) (m : ℕ) (hm : m<d.out) :
    q⊓L x m=q⊓L y m := by
  have hh := (hP.trans (iInf_le _ x)).trans (iInf_le _ y)
  have he : q ≤ sameOutputPrefixValue L d.out x y :=
    (le_inf le_rfl hXY).trans ((le_materialImp_iff_r126 _ _ _).mp hh)
  exact (le_bitEq_iff_r126 _ _ _).mp (he.trans (iInf_le (fun j : Fin d.out => bitEq (L x j.val) (L y j.val)) ⟨m,hm⟩))

theorem actualRawWindow_errorBudget_r360 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N)
    (hH : (T.level N).weight H≠⊥) (hq : q≤(T.level N).weight H)
    (x : ℕ → B) (hX : q≤bitsBelowValue x (actualSourceUnion T)) (k n : ℕ) (hk : k+1<N) :
    q≤nameErrorBudget true (dyadicGapDen k) n
      (bitsMeet (crispStageWindow H k) (L (actualPaddedInput T x)))
      (bitsMeet (crispStageWindow H k) (L (actualLocalRawInput T H k x))) := by
  let d := historyStage H k
  let e := historyStage H (k+1)
  let X := actualPaddedInput T x
  let Z := actualLocalRawInput T H k x
  let Y := actualPrefixPatch d.left Z X
  let W : ℕ → B := crispStageWindow H k
  have hk' : k<N := by omega
  by_cases hn : d.out≤n
  · have hG : q≤actualStageGraftValue L k d :=
      hq.trans ((T.stageOfHistoryValue_r353 H k hk').trans
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    have hM : q≤actualMiddleMatch X d.left d.right d.pad :=
      (le_actualMiddleMatch_iff_r351 _ _ _ _ _).mpr (fun m hl hr =>
        actualPaddedInput_middle_mask_r359 T H hH hq x hX k m hk hl hr)
    have hE : q≤nameErrorBudget true (dyadicGapDen k) n (L X) (L Y) := by
      have h := stageGraft_apply_r360 hG X X Z n hn hM
      simpa only [actualPrefixPatch_self_r347,Y] using h
    have hW := hE.trans (nameErrorBudget_mask_r298 true (dyadicGapDen k) n (L X) (L Y) W)
    have hP : q≤actualStagePrefixValue L e :=
      hq.trans ((T.stageOfHistoryValue_r353 H (k+1) hk).trans
        (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    have hOut : q≤realEqValue (bitsMeet W (L Y)) (bitsMeet W (L Z)) := by
      apply (le_realEqValue_iff_r126 _ _ _).mpr
      intro m
      by_cases hm : m∈groundStageWindow H k
      · have hCut : m<e.out := (Finset.mem_Ico.mp hm).2
        exact mask_inf_congr_r126 rfl (stagePrefix_apply_r360 hP
          (actualGraftInput_agrees_prefix_r359 T H hq x hX k hk) m hCut)
      · simp only [bitsMeet,W,crispStageWindow,crispTruth,ite_eq_right hm,bot_inf_eq]
    have hId := nameErrorBudget_mask_r313 true (dyadicGapDen k) n
      (le_top.trans_eq (realEqValue_refl_r127 (bitsMeet W (L X))).symm) hOut
    exact ((le_inf le_rfl hW).trans_eq hId).trans inf_le_right
  · have hZero (Z : ℕ → B) : ∀ m<n, q⊓bitsMeet W Z m=q⊓crispTruth B (m∈(∅ : Set ℕ)) := by
      intro m hm
      have hN : m∉groundStageWindow H k := fun h => hn (((Finset.mem_Ico.mp h).1).trans hm.le)
      simp [bitsMeet,W,crispStageWindow,crispTruth,hN]
    have hG : GroundBudgetHolds true (xorSet (∅ : Set ℕ) ∅) ∅ (dyadicGapDen k) n := by
      simpa [xorSet] using (GroundBudgetHolds.refl_r228 true (∅ : Set ℕ) (dyadicGapDen k) n)
    exact nameErrorBudget_crispPrefix_complete_r340 true (dyadicGapDen k) n (hZero (L X)) (hZero (L Z)) hG

end SetLanguage
end JSP000933
