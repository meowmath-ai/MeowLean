import JSP000930NegativeTwoStepBaseCoherence

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport

variable {B N M : Type} [CompleteBooleanAlgebra B]
  (Q : ValuedPoset B N) (S : ValuedPoset (TotalBA Q) M)

theorem augmentedDenseMap_support (x : TotalBA S) :
    supportProjection (augmentedQ Q S) ((augmentedDenseMap Q S).pullIso x) =
      supportProjection Q (supportProjection S x) := by
  let F := (augmentedDenseMap Q S).pullIso
  apply le_antisymm
  · apply (supportProjection_le_iff_r428 _ _ _).mpr
    rw [← augmentedDenseMap_base Q S]
    apply F.monotone
    apply (supportProjection_le_iff_r428 S _ _).mp
    exact (supportProjection_le_iff_r428 Q _ _).mp le_rfl
  · apply (supportProjection_le_iff_r428 Q _ _).mpr
    apply (supportProjection_le_iff_r428 S _ _).mpr
    apply F.le_iff_le.mp
    rw [augmentedDenseMap_base Q S]
    exact (supportProjection_le_iff_r428 _ _ _).mp le_rfl

end JSP000930.Negative
