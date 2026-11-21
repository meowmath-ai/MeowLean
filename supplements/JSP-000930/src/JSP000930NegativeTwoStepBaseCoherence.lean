import JSP000930NegativeActualTwoStepDenseMap

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport

variable {B N M : Type} [CompleteBooleanAlgebra B]
  (Q : ValuedPoset B N) (S : ValuedPoset (TotalBA Q) M)

theorem augmentedDenseMap_basis_iff (p : TotalCondition (augmentedQ Q S))
    (x : TotalBA S) :
    imageCondition p ≤ (augmentedDenseMap Q S).pullIso x ↔
      imageCondition ((augmentedDenseMap Q S).map p) ≤ x := by
  rw [image_le_iff_member,image_le_iff_member]
  exact (augmentedDenseMap Q S).mem_pull x p

theorem augmentedDenseMap_base (b : B) :
    (augmentedDenseMap Q S).pullIso (baseEmbed S (baseEmbed Q b)) =
      baseEmbed (augmentedQ Q S) b := by
  have h (p : TotalCondition (augmentedQ Q S)) :
      imageCondition p ≤ (augmentedDenseMap Q S).pullIso
        (baseEmbed S (baseEmbed Q b)) ↔ p.mask ≤ b := by
    rw [augmentedDenseMap_basis_iff,baseEmbed_reflects_mask_r427]
    change imageCondition (augmentedFirst Q S p) ≤ baseEmbed Q b ↔ p.mask ≤ b
    exact baseEmbed_reflects_mask_r427 (augmentedFirst Q S p) b
  apply le_antisymm <;> apply le_of_image_tests
  · intro p hp
    exact image_le_baseEmbed_r427 p b ((h p).mp hp)
  · intro p hp
    exact (h p).mpr ((baseEmbed_reflects_mask_r427 p b).mp hp)

end JSP000930.Negative
