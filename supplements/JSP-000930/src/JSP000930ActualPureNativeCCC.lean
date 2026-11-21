import JSP000930ActualNativeWetzelLimitBases

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.RelativeOCA
open scoped Cardinal

noncomputable def nativeWetzelBoundedTower (a : GroundContinuumSuccIndex) (hL : CheckedGroundLimit a) :
    CompleteStageTower (nativePrefixBase a) (fun i : {j : GroundContinuumSuccIndex // j<a} =>
      NativeWetzelPrefixRO i.val) where
  stage i := nativePrefixComplete i.property.le
  base i := nativePrefixBase i.val
  shift i j hij := nativePrefixComplete hij
  base_coherent i x := basedPrefix_base_commutes actualWetzelTail (wetzel_bot_lt_work i.val)
    ((wetzelWorkStage_le_iff _ _).mpr i.property.le) x
  shift_coherent i j hij x := nativePrefixComplete_comp hij j.property.le x
  final_dense x hx := by
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 x hx
    obtain ⟨i,hi,r,hr⟩ := nativeWetzelEarlierBasis hL.1 hL.2 p
    refine ⟨⟨i,hi⟩,imageCondition r,?_,?_⟩
    · change (nativePrefixComplete hi.le).toFun (imageCondition r) ≠ ⊥
      rw [hr]
      exact imageCondition_ne_bot_r50 p
    · change (nativePrefixComplete hi.le).toFun (imageCondition r) ≤ x
      rwa [hr]

theorem nativeWetzelBoundedTower_continuous (a : GroundContinuumSuccIndex) (hL : CheckedGroundLimit a) :
    ContinuousStageTower (nativeWetzelBoundedTower a hL) := by
  intro t ht x hx
  obtain ⟨k,hk⟩ := ht.1
  have h₀ : ∃ i : GroundContinuumSuccIndex,i<t.val := ⟨k.val,hk⟩
  have hLt (i : GroundContinuumSuccIndex) (hi : i<t.val) : ∃ j,i<j ∧ j<t.val := by
    obtain ⟨j,hij,hjt⟩ := ht.2 ⟨i,hi.trans t.property⟩ hi
    exact ⟨j.val,hij,hjt⟩
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 x hx
  obtain ⟨i,hi,r,hr⟩ := nativeWetzelEarlierBasis h₀ hLt p
  refine ⟨⟨i,hi.trans t.property⟩,hi,imageCondition r,imageCondition_ne_bot_r50 r,?_⟩
  change (nativePrefixComplete hi.le).toFun (imageCondition r) ≤ x
  rwa [hr]

theorem nativePrefixReduce_eq (a : GroundContinuumSuccIndex) :
    prefixReduce (nativePrefixBase a) = (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project := by
  funext x
  have h (u : PreparedBA) : prefixReduce (nativePrefixBase a) x ≤ u ↔
      (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project x ≤ u := by
    rw [prefixReduce_le_iff,(prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project_gc] <;> rfl
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

theorem actualWetzelPrefixCCC_small_limit (a : GroundContinuumSuccIndex)
    (hL : CheckedGroundLimit a) (hPrev : ∀ j<a,ActualWetzelPrefixCCC j) :
    ActualWetzelPrefixCCC a := by
  let I := {j : GroundContinuumSuccIndex // j<a}
  letI : Nonempty I := ⟨⟨Classical.choose hL.1,Classical.choose_spec hL.1⟩⟩
  have hI : Cardinal.mk I ≤ 𝔠 := Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a)
  change ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project
  rw [← nativePrefixReduce_eq a]
  apply projectedCCC_of_prepared_small_continuousTower (nativePrefixBase a)
    (nativeWetzelBoundedTower a hL) (nativeWetzelBoundedTower_continuous a hL) hI
  intro i
  change ProjectedAntichainCCC (prefixReduce (nativePrefixBase i.val))
  rw [nativePrefixReduce_eq]
  exact hPrev i.val i.property

noncomputable def actualNativeWetzelκTower :
    CompleteStageTower (basedBaseEmbed actualWetzelTail) NativeWetzelPrefixRO where
  stage := nativePrefixIntoWhole
  base := nativePrefixBase
  shift _ _ h := nativePrefixComplete h
  base_coherent i x := basedWhole_base_commutes actualWetzelTail (wetzel_bot_lt_work i) x
  shift_coherent i j h x := whole_after_prefixReduction930 ((wetzelWorkStage_le_iff _ _).mpr h) x
  final_dense x hx := by
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 x hx
    obtain ⟨i,r,hr⟩ := nativeWetzelFinalEarlierBasis p
    exact ⟨i,imageCondition r,hr.symm ▸ imageCondition_ne_bot_r50 p,hr.trans_le hp⟩

theorem actualWetzelWhole_projectedCCC (h : ∀ a,ActualWetzelPrefixCCC a) :
    ProjectedAntichainCCC (basedMaskRealization actualWetzelTail).project := by
  have hPI : prefixReduce (basedBaseEmbed actualWetzelTail) = (basedMaskRealization actualWetzelTail).project := by
    funext x
    have hP (u : PreparedBA) : prefixReduce (basedBaseEmbed actualWetzelTail) x ≤ u ↔
        (basedMaskRealization actualWetzelTail).project x ≤ u := by
      rw [prefixReduce_le_iff,(basedMaskRealization actualWetzelTail).project_gc] <;> rfl
    exact le_antisymm ((hP _).mpr le_rfl) ((hP _).mp le_rfl)
  rw [← hPI]
  apply projectedCCC_of_checkedKappa_tower prepared_boundsOmegaOne_r432 actual_prepared_boundsSmallKappa_r473
    (basedBaseEmbed actualWetzelTail) actualNativeWetzelκTower
  intro i
  change ProjectedAntichainCCC (prefixReduce (nativePrefixBase i))
  rw [nativePrefixReduce_eq]
  exact h i

end JSP000930.Negative
