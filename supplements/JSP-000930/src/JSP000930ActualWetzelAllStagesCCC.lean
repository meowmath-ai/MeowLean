import JSP000930ActualJointUncountableLimit

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.RelativeOCA
open JSP000933.MarkedForcing JSP000933.ForcingTransport

theorem actualWetzelStage_cases (a : GroundContinuumSuccIndex) :
    a=firstGroundWetzelStage ∨ (∃ b,wetzelGroundNext b=a) ∨ CheckedGroundLimit a := by
  classical
  by_cases h : ∃ b,b<a
  · right
    by_cases hM : ∃ b,b<a ∧ ∀ j,j<a → j≤b
    · left
      obtain ⟨b,hb,hMax⟩ := hM
      have hn : wetzelGroundNext b≤a := wetzelGroundNext_le_of_lt hb
      refine ⟨b,le_antisymm hn ?_⟩
      by_contra hNot
      have hLater : wetzelGroundNext b<a := lt_of_not_ge hNot
      exact ((wetzelGroundNext_spec b b).mpr le_rfl).not_ge (hMax _ hLater)
    · right
      refine ⟨h,?_⟩
      intro j hj
      by_contra hNo
      exact hM ⟨j,hj,fun k hk => le_of_not_gt (fun hjk => hNo ⟨k,hjk,hk⟩)⟩
  · left
    exact le_antisymm (le_of_not_gt (fun he => h ⟨firstGroundWetzelStage,he⟩))
      (firstGroundWetzelStage_le a)

theorem actualWetzelAllStagesCCC (a : GroundContinuumSuccIndex) :
    ActualWetzelPrefixCCC a ∧ ActualWetzelJointCCC a := by
  have hWF : WellFounded (fun i j : GroundContinuumSuccIndex => i < j) := wellFounded_lt
  induction a using hWF.induction with
  | h a ih =>
    rcases actualWetzelStage_cases a with hF | ⟨b,hS⟩ | hL
    · subst a
      exact ⟨actualFirstWorkingPrefix_projectedCCC,fun s _ => actualFirstWorkingPrefix_jointCCC s⟩
    · subst a
      have hb : b<wetzelGroundNext b := (wetzelGroundNext_spec b b).mpr le_rfl
      exact actualWetzelSuccessor_both b
        (fun j hj => (ih j (hj.trans_lt hb)).1) (ih b hb).2
    · exact ⟨actualWetzelPrefixCCC_small_limit a hL (fun j hj => (ih j hj).1),
        actualWetzelJointCCC_limit a hL (fun j hj => (ih j hj).1) (fun j hj => (ih j hj).2)⟩

theorem actualWetzelFinalCCC :
    ForcesRelativeCCC (nativeWetzelWholeQ actualWetzelRest) :=
  nativeWetzelWholeQ_relativeCCC actualWetzelRest (actualWetzelWhole_projectedCCC
    (fun a => (actualWetzelAllStagesCCC a).1))

theorem actualWetzelAllPriorBounds (a : GroundContinuumSuccIndex) :
    BoundsSmallKappaNames (ActualWorkBA a) :=
  nativeWetzelPrefix_boundsKappa actualWetzelRest a (actualWetzelAllStagesCCC a).1

end JSP000930.Negative
