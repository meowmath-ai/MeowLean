import JSP000930IndependentFactorTransport

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen
open JSP000933.MarkedForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B N J : Type} [NontrivialCompleteBooleanAlgebra B]

def denseForcingMapOfIso930 {P R : Type} [Preorder P] [Preorder R]
    (e : P ≃o R) : DenseForcingMap P R where
  map := e
  monotone := e.monotone
  dense := fun q => ⟨e.symm q,by rw [e.apply_symm_apply]⟩
  reflect_compatible := by
    intro p q h
    obtain ⟨r,hrp,hrq⟩ := h
    exact ⟨e.symm r,by simpa only [e.symm_apply_apply] using e.symm.monotone hrp,
      by simpa only [e.symm_apply_apply] using e.symm.monotone hrq⟩

theorem densePull_comp930 {P Q R : Type} [Preorder P] [Preorder Q] [Preorder R]
    (F : DenseForcingMap P Q) (G : DenseForcingMap Q R) (u : RO R) :
    (denseForcingMap_comp930 F G).pullIso u = F.pullIso (G.pullIso u) := by
  apply Heyting.Regular.coe_injective
  rfl

noncomputable def analyticThenCohenDenseMap (Q : ValuedPoset B N) (X : Type) :
    DenseForcingMap (TotalCondition (valuedPair Q (valuedCohen B X)))
      (TotalCondition (valuedCohen (TotalBA Q) X)) :=
  change_valuedCohen (markedCompleteValueMap Q) X ▸ pairIteratedDenseMap Q (valuedCohen B X)

noncomputable def cohenThenAnalyticDenseMap (X : Type)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) :
    DenseForcingMap (TotalCondition (valuedPair (supportedSymbolicQ site H A) (valuedCohen B X)))
      (TotalCondition (supportedSymbolicQ
        (fun j => (site j).map (markedCompleteValueMap (valuedCohen B X)))
        (fun j n => (H j n).map (markedCompleteValueMap (valuedCohen B X))) A)) := by
  let P := supportedSymbolicQ site H A
  let Q := valuedCohen B X
  let D : DenseForcingMap (TotalCondition (valuedPair Q P))
      (TotalCondition (supportedSymbolicQ
        (fun j => (site j).map (markedCompleteValueMap Q))
        (fun j n => (H j n).map (markedCompleteValueMap Q)) A)) :=
    change_supportedSymbolic (markedCompleteValueMap Q) site H A ▸ pairIteratedDenseMap Q P
  exact denseForcingMap_comp930 (denseForcingMapOfIso930 (pairSwapCondition P Q)) D

end JSP000930.Negative
