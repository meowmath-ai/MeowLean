import JSP000930AugmentedActualHistoryChart

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport

abbrev LiveRowModel (a : GroundContinuumSuccIndex) :=
  TotalBA ((actualWorkingInputs a).row a)

noncomputable def actualWorkRowMap (a : GroundContinuumSuccIndex) :
    CompleteValueMap (ActualWorkBA a) (LiveRowModel a) :=
  markedCompleteValueMap ((actualWorkingInputs a).row a)

noncomputable def beforeFreshSite (a j : GroundContinuumSuccIndex) : ComplexBits (LiveRowModel a) :=
  ((actualWorkingInputs a).site j).map (actualWorkRowMap a)

noncomputable def beforeFreshPalette (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (r : s) (j : GroundContinuumSuccIndex) (n : ℕ) :
    ComplexBits (LiveRowModel a) :=
  (actualWetzelRowPalette a r.val j n).map (actualWorkRowMap a)

noncomputable def beforeFreshCohenTest (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :=
  EarlierAnalyticProduct (beforeFreshSite a) (beforeFreshPalette a s) (WorkingDomain a)

theorem beforeFreshCohenTest_eq (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :
    changeValuedBase (actualWorkRowMap a) (actualSurvivorProduct a s) = beforeFreshCohenTest a s := by
  unfold actualSurvivorProduct beforeFreshCohenTest EarlierAnalyticProduct
  rw [change_rowProduct930]
  apply congrArg (fun f => rowProductQ f)
  funext r
  exact change_supportedSymbolic (actualWorkRowMap a) _ _ _

def castMaskedCondition930 {B N : Type} [CompleteBooleanAlgebra B]
    {P Q : ValuedPoset B N} (h : P=Q) (m : B) (p : MaskedCondition P m) : MaskedCondition Q m :=
  h ▸ p

theorem castMaskedCondition_iso930 {B N : Type} [CompleteBooleanAlgebra B]
    {P Q : ValuedPoset B N} (h : P=Q) (m : B) :
    Nonempty {e : MaskedCondition P m ≃o MaskedCondition Q m //
      ∀ p,e p = castMaskedCondition930 h m p} := by
  cases h
  exact ⟨⟨OrderIso.refl _,fun _ => rfl⟩⟩

noncomputable def beforeFreshCohenMap (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (p : MaskedCondition (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u)) :
    MaskedCondition (beforeFreshCohenTest a s) ((actualWorkPreparedAfterRow a).toFun u) :=
  castMaskedCondition930 (beforeFreshCohenTest_eq a s) _
    (changeValuedBaseMasked930 (actualWorkRowMap a) _ ((actualPreparedAt a).toFun u) p)

theorem beforeFreshCohenMap_mono (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    Monotone (beforeFreshCohenMap a s u) := by
  obtain ⟨⟨e,he⟩⟩ := castMaskedCondition_iso930 (beforeFreshCohenTest_eq a s)
    ((actualWorkPreparedAfterRow a).toFun u)
  intro p q h
  let f := changeValuedBaseMasked930 (actualWorkRowMap a) (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u)
  have hf : f p ≤ f q := changeValuedBaseMasked_mono930 (actualWorkRowMap a) _ _ h
  exact (he (f p)).symm.trans_le ((e.monotone hf).trans_eq (he (f q)))

theorem beforeFreshCohenMap_predense (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    PreservesPredensity (beforeFreshCohenMap a s u) := by
  obtain ⟨⟨e,he⟩⟩ := castMaskedCondition_iso930 (beforeFreshCohenTest_eq a s)
    ((actualWorkPreparedAfterRow a).toFun u)
  have h := preservesPredensity_comp930
    (changeValuedBaseMasked930 (actualWorkRowMap a) (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u))
    e e.monotone
    (independentActiveRow_marked_predensity930 ((actualWorkingInputs a).row a)
      (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u)) (presPred_of_orderIso930 e)
  have hEq : beforeFreshCohenMap a s u =
      e ∘ changeValuedBaseMasked930 (actualWorkRowMap a) (actualSurvivorProduct a s)
        ((actualPreparedAt a).toFun u) := by
    funext p
    exact (he _).symm
  rwa [hEq]

theorem castMaskedCondition_data930 {B N : Type} [CompleteBooleanAlgebra B]
    {P Q : ValuedPoset B N} (h : P=Q) {m : B} (p : MaskedCondition P m) :
    (castMaskedCondition930 h m p).val.mask=p.val.mask ∧
      (castMaskedCondition930 h m p).val.trace=p.val.trace := by
  cases h
  exact ⟨rfl,rfl⟩

theorem beforeFreshCohenMap_data (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (p : MaskedCondition (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u)) :
    (beforeFreshCohenMap a s u p).val.mask=(actualWorkRowMap a).toFun p.val.mask ∧
      (beforeFreshCohenMap a s u p).val.trace=p.val.trace :=
  castMaskedCondition_data930 (beforeFreshCohenTest_eq a s)
    (changeValuedBaseMasked930 (actualWorkRowMap a) _ _ p)

end JSP000930.Negative
