import JSP000930FixedTaggedStageForcing
import JSP000930PositiveActualCohenCoordinates

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Negative.Cohen
open JSP000933.MarkedForcing JSP000933.ForcingTransport JSP000933.RelativeOCA
open JSP000933.PreparedModel JSP000933.OpenGraphForcing

abbrev WorkCohenCoordinate := PaletteRow OmegaOneIndex × ℕ

inductive WetzelMasterLabel where
  | zero
  | bulk (trace : Trace WetzelCoordinate)
  | work (polynomial : Option (SymbolicTrace GroundContinuumSuccIndex))
      (trace : Trace WorkCohenCoordinate)

abbrev WetzelCertifiedLabel := CertifiedStageLabel WetzelMasterLabel

def decodeBulk : WetzelMasterLabel → Option (Trace WetzelCoordinate)
  | .zero => some (emptyTrace _)
  | .bulk q => some q
  | .work .. => none

open scoped Classical in
noncomputable def decodeWork (A : GroundContinuumSuccIndex → Prop) :
    WetzelMasterLabel → Option (SupportedSymbolic GroundContinuumSuccIndex A × Trace WorkCohenCoordinate)
  | .zero => some (⟨none,True.intro⟩,emptyTrace _)
  | .bulk _ => none
  | .work p q => if h : SymbolicLabelAt A p then some (⟨p,h⟩,q) else none

section Bulk
variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def wetzelTaggedBulk : ValuedPoset B WetzelMasterLabel :=
  taggedValuedPoset (valuedCohen B WetzelCoordinate) decodeBulk .zero rfl

noncomputable def wetzelBulkTagDense :
    DenseForcingMap (TotalCondition (wetzelTaggedBulk (B := B)))
      (TotalCondition (valuedCohen B WetzelCoordinate)) :=
  taggedDenseMap (valuedCohen B WetzelCoordinate) decodeBulk .zero rfl .bulk (fun _ => rfl)

end Bulk

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def wetzelRawWork (site : GroundContinuumSuccIndex → ComplexBits B)
    (H : GroundContinuumSuccIndex → ℕ → ComplexBits B) (A : GroundContinuumSuccIndex → Prop) :=
  valuedPair (supportedSymbolicQ site H A) (valuedCohen B WorkCohenCoordinate)

noncomputable def wetzelTaggedWork (site : GroundContinuumSuccIndex → ComplexBits B)
    (H : GroundContinuumSuccIndex → ℕ → ComplexBits B) (A : GroundContinuumSuccIndex → Prop) :
    ValuedPoset B WetzelMasterLabel :=
  taggedValuedPoset (wetzelRawWork site H A) (decodeWork A) .zero rfl

noncomputable def wetzelWorkTagDense (site : GroundContinuumSuccIndex → ComplexBits B)
    (H : GroundContinuumSuccIndex → ℕ → ComplexBits B) (A : GroundContinuumSuccIndex → Prop) :
    DenseForcingMap (TotalCondition (wetzelTaggedWork site H A)) (TotalCondition (wetzelRawWork site H A)) := by
  classical
  refine taggedDenseMap (wetzelRawWork site H A) (decodeWork A) .zero rfl
    (fun v => .work v.1.val v.2) ?_
  rintro ⟨⟨p,h⟩,q⟩
  simp only [decodeWork,dite_eq_left h]

end JSP000930.Negative
