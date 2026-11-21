import JSP000930ActualPreparedTailMasks

namespace JSP000930.Negative

open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA

theorem actualWetzelJointCCC_uncountable_limit (a : GroundContinuumSuccIndex)
    (hL : CheckedGroundLimit a) (hU : ∀ g : ℕ→Set.Iio a,∃ d : Set.Iio a,∀ n,g n<d)
    (hPrev : ∀ j<a,ActualWetzelPrefixCCC j) (hJ : ∀ j<a,ActualWetzelJointCCC j) :
    ActualWetzelJointCCC a := by
  intro s hs
  apply actualSurvivorProduct_of_augmentedCCC
  let K := (↥(Set.Iio a) : Type)
  let J (d : K) := OpenWetzelTail d.val a
  let u (d : K) := preparedJointTailMark a s d
  letI : ∀ d : K,Nonempty (J d) := fun d => ⟨⟨d.val,le_rfl,d.property⟩⟩
  have hB (j : GroundContinuumSuccIndex) (hj : j<a) :
      BoundsSmallKappaNames (ActualWorkBA j) :=
    nativeWetzelPrefix_boundsKappa actualWetzelRest j (hPrev j hj)
  let Qs (d : K) (i : J d) := actualAugmentedQ i.val s
  let C (d : K) : MaskedContinuousTower (actualAugmentedQ a s) (Qs d) (u d) :=
    actualMaskedSurvivorTower d.property hL hB s (u d)
      (fun j hd hj r t hn => preparedJointTailMark_separates a s d hd hj r t hn)
  apply relativeCCC_of_covering_masked_small_limits u (preparedJointTailMark_covers a s hL hU)
    Qs C (fun _ => openWetzelTail_card_le_continuum)
  intro d i
  apply RelativeCCCOn.of_global
  exact actualAugmentedQ_of_stageCCC i.val s (hPrev i.val i.property.2)
    (hJ i.val i.property.2 s (fun r hr => i.property.2.le.trans (hs r hr)))

theorem actualWetzelJointCCC_limit (a : GroundContinuumSuccIndex)
    (hL : CheckedGroundLimit a)
    (hPrev : ∀ j<a,ActualWetzelPrefixCCC j) (hJ : ∀ j<a,ActualWetzelJointCCC j) :
    ActualWetzelJointCCC a := by
  classical
  by_cases h : ∃ g : ℕ → Set.Iio a,∀ j<a,∃ n,j≤(g n).val
  · obtain ⟨g,hg⟩ := h
    exact actualWetzelJointCCC_countable_limit a hL g hg hPrev hJ
  · apply actualWetzelJointCCC_uncountable_limit a hL _ hPrev hJ
    intro g
    by_contra hn
    apply h
    refine ⟨g,?_⟩
    intro j hj
    by_contra hj'
    exact hn ⟨⟨j,hj⟩,fun n => lt_of_not_ge (fun hn => hj' ⟨n,hn⟩)⟩

end JSP000930.Negative
