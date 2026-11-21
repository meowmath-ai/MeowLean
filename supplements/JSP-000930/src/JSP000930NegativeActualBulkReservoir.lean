import JSP000930NegativeDistinctDyadicCutRows
import JSP000930PositiveActualReserveComplexPoint
import JSP000930PositiveNativeGrowthNaturality
import JSP000930PositiveExplicitCutValidityNaturality

open bSet Lattice Cardinal
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.ForcingTransport
  JSP000933.RelativeOCA JSP000930.Positive JSP000930.Positive.Cohen JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

noncomputable def bulkReservoirPoint (i : KappaSiteIndex) : ComplexBits WetzelCohenBA :=
  ⟨dyadicCutBits (B := PreparedBA) (Sum.inl i : WetzelRow),checkedRealBits 0⟩

theorem bulkReservoirPoint_cut (i : KappaSiteIndex) :
    (bulkReservoirPoint i).CutOn ⊤ :=
  ⟨dyadicCut_is_proper (B := PreparedBA) (Sum.inl i : WetzelRow),
    checkedRealBits_properCut 0⟩

theorem bulkReservoirPoints_apart (i j : KappaSiteIndex) (hij : i ≠ j) :
    ((bulkReservoirPoint i).name =ᴮ (bulkReservoirPoint j).name) = (⊥ : WetzelCohenBA) := by
  apply le_bot_iff.mp
  have hd := dyadicCutName_rows_apart (B := PreparedBA)
    (show (Sum.inl i : WetzelRow) ≠ Sum.inl j from fun h => hij (Sum.inl_injective h))
  exact eq_of_eq_pair_left.trans hd.le

theorem liftName_complexSite (F : CompleteValueMap B C) (x : ComplexBits B) :
    (coefficientsOfValueMap F).liftName x.name = (mapComplexBits F x).name := by
  change (coefficientsOfValueMap F).liftName
      (pair (weightedRationalSet x.re) (weightedRationalSet x.im)) =
    pair (weightedRationalSet fun q => F.toFun (x.re q))
      (weightedRationalSet fun q => F.toFun (x.im q))
  rw [liftName_pair,liftName_cut,liftName_cut] <;> rfl

theorem properSite_map (F : CompleteValueMap B C) (x : ComplexBits B) {p : B}
    (h : x.CutOn p) : (mapComplexBits F x).CutOn (F.toFun p) := by
  have hMap (u : RatPresentation → B) (hu : ProperCutOn p u) :
      ProperCutOn (F.toFun p) (fun q => F.toFun (u q)) := by
    apply (le_properCutValue_iff _ _).mp
    rw [← properCutValue_map F]
    exact F.monotone ((le_properCutValue_iff u p).mpr hu)
  exact ⟨hMap _ h.1,hMap _ h.2⟩

theorem exists_newSite_with_actual_bulk_reservoir
    {I : Type} (hB : BoundsSmallKappaNames B) (hI : Cardinal.mk I < GroundContinuumSucc)
    (F : CompleteValueMap WetzelCohenBA B) (old : I → ComplexBits B)
    (z : ComplexBits B) (p : B) (hz : z.CutOn p) :
    ∃ y : ComplexBits B, y.CutOn ⊤ ∧
      (∀ i, ((y.name =ᴮ (old i).name) : B) = ⊥) ∧
      p ≤ (⨆ i,z.name =ᴮ (old i).name) ⊔ (z.name =ᴮ y.name) := by
  let u (i : KappaSiteIndex) := mapComplexBits F (bulkReservoirPoint i)
  apply exists_newSite_captures_trial hB hI old u ?_ ?_ z p hz
  · intro i
    have h := properSite_map F (bulkReservoirPoint i) (bulkReservoirPoint_cut i)
    rw [F.map_top] at h
    exact h
  · intro i j hij
    change ((mapComplexBits F (bulkReservoirPoint i)).name =ᴮ
      (mapComplexBits F (bulkReservoirPoint j)).name) = ⊥
    rw [← liftName_complexSite F,← liftName_complexSite F,
      (coefficientsOfValueMap F).liftName_eq]
    change F.toFun ((bulkReservoirPoint i).name =ᴮ (bulkReservoirPoint j).name) = ⊥
    rw [bulkReservoirPoints_apart i j hij,F.map_bot]

end JSP000930.Negative
