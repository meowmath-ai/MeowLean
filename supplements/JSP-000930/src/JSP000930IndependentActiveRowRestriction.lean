import JSP000930HistoricalReadyTrial

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing

variable {B N M : Type} [NontrivialCompleteBooleanAlgebra B]

def pairSecond930 (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition (valuedPair P Q)) : TotalCondition Q :=
  ⟨p.mask,p.trace.2,p.nonzero,p.valid.trans inf_le_right⟩

noncomputable def pairSecondRestriction (P : ValuedPoset B N) (Q : ValuedPoset B M) :
    RestrictionMap (TotalCondition (valuedPair P Q)) (TotalCondition Q) where
  toFun := pairSecond930 P Q
  monotone := fun _ _ h => ⟨h.1,h.2.trans inf_le_right⟩
  onto := by
    intro q
    let p : TotalCondition (valuedPair P Q) :=
      ⟨q.mask,(P.weakest,q.trace),q.nonzero,le_inf (le_top.trans_eq P.weakest_valid.symm) q.valid⟩
    exact ⟨p,by cases q; rfl⟩
  lift := by
    intro p q hq
    have hP : q.mask ≤ P.valid p.trace.1 := hq.1.trans (p.valid.trans inf_le_left)
    let r : TotalCondition (valuedPair P Q) :=
      ⟨q.mask,(p.trace.1,q.trace),q.nonzero,le_inf hP q.valid⟩
    exact ⟨r,⟨hq.1,le_inf (hP.trans (P.refl _)) hq.2⟩,le_rfl⟩

theorem pairSecondRestriction_base (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (b : B) :
    (pairSecondRestriction P Q).boolPullback (baseEmbed Q b) = baseEmbed (valuedPair P Q) b := by
  have ht (p : TotalCondition (valuedPair P Q)) :
      imageCondition p ≤ (pairSecondRestriction P Q).boolPullback (baseEmbed Q b) ↔
      imageCondition p ≤ baseEmbed (valuedPair P Q) b := by
    rw [image_le_regular_pullback,baseEmbed_reflects_mask_r427,baseEmbed_reflects_mask_r427] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
     (le_of_image_tests (fun p => (ht p).mpr))

noncomputable def independentActiveRowMap (P : ValuedPoset B N) (Q : ValuedPoset B M) :
    CompleteValueMap (TotalBA Q) (TotalBA (changeValuedBase (markedCompleteValueMap P) Q)) :=
  composeCompleteValueMaps (pairSecondRestriction P Q).completeValueMap
    (completeMapOfOrderIso930 (pairIteratedDenseMap P Q).pullIso.symm)

theorem independentActiveRowMap_base (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (b : B) :
    (independentActiveRowMap P Q).toFun (baseEmbed Q b) =
      baseEmbed (changeValuedBase (markedCompleteValueMap P) Q) (baseEmbed P b) := by
  let D := pairIteratedDenseMap P Q
  apply D.pullIso.injective
  change D.pullIso (D.pullIso.symm ((pairSecondRestriction P Q).boolPullback (baseEmbed Q b))) = _
  rw [OrderIso.apply_symm_apply,pairSecondRestriction_base,pairIteratedDenseMap_base]

end JSP000930.Negative
