import JSP000930MarkedOrderIsoCharts

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport JSP000933.RelativeOCA

noncomputable def actualSurvivorHistoryChart (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :
    WeightedPosetChart (normalizedSurvivorQ a s) (actualSurvivorProduct a s) where
  values := (actualPrefixHistoryIso a).symm
  label := Equiv.refl _
  valid p := (actualPrefixHistoryIso a).symm_apply_apply ((actualSurvivorProduct a s).valid p)
  refines p q := (actualPrefixHistoryIso a).symm_apply_apply ((actualSurvivorProduct a s).refines p q)

noncomputable def actualAugmentedHistoryDense (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :
    DenseForcingMap (TotalCondition (actualAugmentedQ a s)) (TotalCondition (actualSurvivorProduct a s)) :=
  denseForcingMap_comp930 (augmentedDenseMap (actualPrefixQ a) (normalizedSurvivorQ a s))
    (denseForcingMapOfIso930 (actualSurvivorHistoryChart a s).totalIso)

theorem actualAugmentedHistoryDense_rect (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (p : TotalCondition (actualAugmentedQ a s)) :
    ((actualAugmentedHistoryDense a s).map p).mask =
      (actualPrefixHistoryIso a).symm (traceRectangle (actualPrefixQ a) p.trace.1 p.mask) := by
  change (actualPrefixHistoryIso a).symm
    (((augmentedDenseMap (actualPrefixQ a) (normalizedSurvivorQ a s)).map p).mask) = _
  rw [actualAugmentedDense_basicMask]

theorem actualAugmentedHistoryDense_mask_iff (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (p : TotalCondition (actualAugmentedQ a s)) (u : PreparedBA) :
    ((actualAugmentedHistoryDense a s).map p).mask ≤ (actualPreparedAt a).toFun u ↔ p.mask≤u := by
  let E := actualPrefixHistoryIso a
  have hu : E ((actualPreparedAt a).toFun u) = baseEmbed (actualPrefixQ a) u :=
    actualPreparedAt_as_native_mask a u
  rw [actualAugmentedHistoryDense_rect,← E.le_iff_le,E.apply_symm_apply,hu]
  rw [augmented_rectangle_image _ _ p.nonzero (p.valid.trans inf_le_left)]
  exact baseEmbed_reflects_mask_r427 _ _

noncomputable def actualAugmentedMarkedHistoryDense (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    DenseForcingMap (MaskedCondition (actualAugmentedQ a s) u)
      (MaskedCondition (actualSurvivorProduct a s) ((actualPreparedAt a).toFun u)) where
  map p := ⟨(actualAugmentedHistoryDense a s).map p.val,
    (actualAugmentedHistoryDense_mask_iff a s p.val u).mpr p.property⟩
  monotone := fun _ _ h => (actualAugmentedHistoryDense a s).monotone h
  dense := by
    intro q
    obtain ⟨p,hp⟩ := (actualAugmentedHistoryDense a s).dense q.val
    exact ⟨⟨p,(actualAugmentedHistoryDense_mask_iff a s p u).mp (hp.1.trans q.property)⟩,hp⟩
  reflect_compatible := by
    intro p q
    rintro ⟨r,hrp,hrq⟩
    obtain ⟨v,hvp,hvq⟩ := (actualAugmentedHistoryDense a s).reflect_compatible ⟨r.val,hrp,hrq⟩
    exact ⟨⟨v,hvp.1.trans p.property⟩,hvp,hvq⟩

theorem actualAugmentedHistoryDense_mask_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : TotalCondition (actualAugmentedQ a s)) :
    ((actualAugmentedHistoryDense b s).map (actualAugmentedInclude hab s p)).mask =
      (actualHistoryShift hab).toFun (((actualAugmentedHistoryDense a s).map p).mask) := by
  rw [actualAugmentedHistoryDense_rect,actualAugmentedHistoryDense_rect]
  apply (actualPrefixHistoryIso b).injective
  change actualPrefixHistoryIso b ((actualPrefixHistoryIso b).symm
      (traceRectangle (actualPrefixQ b) (actualPrefixIncludeTrace hab p.trace.1) p.mask)) =
    actualPrefixHistoryIso b ((actualHistoryShift hab).toFun ((actualPrefixHistoryIso a).symm
      (traceRectangle (actualPrefixQ a) p.trace.1 p.mask)))
  rw [OrderIso.apply_symm_apply,← actualPrefixHistoryIso_shift,OrderIso.apply_symm_apply,
    actualPrefixQuotientShift_rectangle]

end JSP000930.Negative
