import JSP000930CertifiedWeightedStage
import JSP000933NativeMarkedSuccessor

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.ForcingTransport CertifiedStageLabel

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def certifiedQ (Q : ValuedPoset B N) : ValuedPoset B (CertifiedStageLabel N) :=
  staticValuedPoset (admits Q) (admits_mono Q) (admits_top Q)

theorem certifiedTotal_le_iff (Q : ValuedPoset B N) (p q : TotalCondition (certifiedQ Q)) :
    p ≤ q ↔ p.mask ≤ q.mask ∧ p.trace ≤ q.trace := by
  constructor
  · intro h
    exact ⟨h.1,((staticValuedPoset_refines_iff _ _ _ p.nonzero _ _).mp h.2).1⟩
  · intro h
    exact ⟨h.1,(staticValuedPoset_refines_iff _ _ _ p.nonzero _ _).mpr ⟨h.2,p.valid⟩⟩

end JSP000930.Negative
