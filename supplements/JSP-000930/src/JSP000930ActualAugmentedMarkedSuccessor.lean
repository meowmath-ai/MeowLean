import JSP000930FreshCohenNativeMarkedChart

namespace JSP000930.Negative

open JSP000930.MixedPalettes JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport JSP000933.RelativeOCA

noncomputable def actualAugmentedLocalArrow {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (hB : ∀ j<b,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    LocalTraceInclusion (actualAugmentedQ a s) (actualAugmentedQ b s) u where
  label := actualAugmentedIncludeLabel hab s
  valid p := congrArg (fun x => u ⊓ x) (actualAugmented_valid_transport hab s p)
  refines p q := congrArg (fun x => u ⊓ x) (actualAugmented_refines_transport hab s p q)
  reflectCommon p q := inf_le_inf le_rfl (actualAugmented_common_backward hab hB s p q)

theorem actualAugmentedLocalArrow_value {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (hB : ∀ j<b,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (p : MaskedCondition (actualAugmentedQ a s) u) :
    ((actualAugmentedLocalArrow hab hB s u).insideMap p).val = actualAugmentedInclude hab s p.val :=
  totalCondition_eq_of_data _ _ rfl rfl

theorem actualAugmented_nextPredense_onMark (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (hSep : ∀ i j : s,i≠j → u ≤ (labelAgreement (preparedWetzelRows i.val a) (preparedWetzelRows j.val a))ᶜ)
    (hB : ∀ j≤a,BoundsSmallKappaNames (ActualWorkBA j)) :
    PreservesPredensity (actualAugmentedLocalArrow ((wetzelGroundNext_spec a a).mpr le_rfl).le
      (fun j hj => hB j ((wetzelGroundNext_spec a j).mp hj)) s u).insideMap := by
  let b := wetzelGroundNext a
  let hab : a≤b := ((wetzelGroundNext_spec a a).mpr le_rfl).le
  let C := actualAugmentedLocalArrow hab (fun j hj => hB j ((wetzelGroundNext_spec a j).mp hj)) s u
  let D := actualAugmentedMarkedHistoryDense a s u
  let E := actualAugmentedMarkedHistoryDense b s u
  let g₁ := beforeFreshCohenMap a s u
  let g₂ := realFreshCohenMap a s u
  let g₃ := freshCohenToNativeMarked a s u
  let g := g₃ ∘ g₂ ∘ g₁
  have h1 := beforeFreshCohenMap_mono a s u
  have h2 := realFreshCohenMap_mono a s u
  have h12 := preservesPredensity_comp930 g₁ g₂ h2 (beforeFreshCohenMap_predense a s u)
    (realFreshCohenMap_predense a s u hSep hB)
  have h123 : PreservesPredensity g := preservesPredensity_comp930 (g₂ ∘ g₁) g₃
    g₃.monotone h12 (presPred_of_orderIso930 g₃)
  apply predensity_through_dense_charts930 D E C.insideMap g _ (g₃.monotone.comp (h2.comp h1)) h123
  intro p
  let q := D.map p
  let r := g₁ q
  let t := g₂ r
  have hr := beforeFreshCohenMap_data a s u q
  have hg : (g q).val = (freshCohenToNativeChart a s).totalIso t.val :=
    freshCohenToNativeMarked_data a s u t
  have hE : (E.map (C.insideMap p)).val =
      (actualAugmentedHistoryDense b s).map (actualAugmentedInclude hab s p.val) := by
    change (actualAugmentedHistoryDense b s).map (C.insideMap p).val = _
    rw [actualAugmentedLocalArrow_value]
  apply Subtype.ext
  change (E.map (C.insideMap p)).val = (g q).val
  rw [hE,hg]
  apply totalCondition_eq_of_data
  · rw [actualAugmentedHistoryDense_mask_transport]
    change (actualHistoryShift hab).toFun q.val.mask =
      createdCohenIsoToHistory a ((stageCohenMap (LiveRowModel a)).toFun r.val.mask)
    rw [hr.1,createdCohenIsoToHistory_apply]
    exact (createdCohenToHistory_base a q.val.mask).symm
  · funext i
    apply Subtype.ext
    change (q.val.trace i).val = (r.val.trace i).val
    rw [hr.2]

end JSP000930.Negative
