import JSP000930RelativeCCCBaseCoherentDense

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B C D N M X : Type} [NontrivialCompleteBooleanAlgebra B]
variable [CompleteBooleanAlgebra C] [CompleteBooleanAlgebra D]

theorem changeValuedBase_comp_exact (F : CompleteValueMap B C) (G : CompleteValueMap C D)
    (Q : ValuedPoset B N) :
    changeValuedBase G (changeValuedBase F Q) = changeValuedBase (composeCompleteValueMaps F G) Q := by
  apply valuedPoset_ext_values <;> rfl

theorem relativeCCC_analytic_with_cohen (hB : BoundsCountableOmegaOneNames B)
    (P : ValuedPoset B N) (hP : ForcesRelativeCCC P) :
    ForcesRelativeCCC (valuedPair P (valuedCohen B X)) :=
  relativeCCC_pair_swap (valuedCohen B X) P (relativeCCC_cohen_pair hB P hP)

theorem relativeCCC_survivor_after_actual_work (hB : BoundsCountableOmegaOneNames B)
    (P : ValuedPoset B N) (Q : ValuedPoset B M) (hP : ForcesRelativeCCC P)
    (hJoint : ForcesRelativeCCC (valuedPair P Q)) :
    ForcesRelativeCCC
      (changeValuedBase (composeCompleteValueMaps (markedCompleteValueMap P)
        (markedCompleteValueMap (valuedCohen (TotalBA P) X))) Q) := by
  let F := markedCompleteValueMap P
  have hR := relativeCCC_after_left_of_product P Q hJoint
  have hB₁ := relativeCCC_preserves_boundsOmegaOne_r436 P hB hP
  have hC := relativeCCC_after_cohen (X:=X) hB₁ (changeValuedBase F Q) hR
  rw [changeValuedBase_comp_exact] at hC
  exact hC

theorem actualWork_preserves_omegaOne (hB : BoundsCountableOmegaOneNames B)
    (P : ValuedPoset B N) (hP : ForcesRelativeCCC P) :
    BoundsCountableOmegaOneNames (CohenBA (TotalBA P) X) :=
  relativeCCC_preserves_boundsOmegaOne_r436 _
    (relativeCCC_preserves_boundsOmegaOne_r436 P hB hP)
    (cohen_forcesRelativeCCC (relativeCCC_preserves_boundsOmegaOne_r436 P hB hP))

end JSP000930.Negative
