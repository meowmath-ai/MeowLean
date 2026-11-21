import JSP000930NegativeAllPreparedSmallContinuousLimits
import JSP000930PositiveActualCohenContinuum
import JSP000930PositiveMixedEnumerationInjection

open Cardinal

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.MarkedForcing JSP000933.ForcingTransport JSP000933.PreparedModel
  JSP000930.Positive JSP000930.Positive.Cohen

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem supportProjection_eq_prefixReduce (Q : ValuedPoset B N)
    (F : CompleteValueMap B (TotalBA Q)) (hF : ∀ b,F.toFun b = baseEmbed Q b) :
    supportProjection Q = prefixReduce F := by
  funext x
  have h (b : B) : supportProjection Q x ≤ b ↔ prefixReduce F x ≤ b := by
    rw [supportProjection_le_iff_r428,prefixReduce_le_iff,hF]
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

theorem relativeCCC_iff_prefixReduce (Q : ValuedPoset B N)
    (F : CompleteValueMap B (TotalBA Q)) (hF : ∀ b,F.toFun b = baseEmbed Q b) :
    ForcesRelativeCCC Q ↔ ProjectedAntichainCCC (prefixReduce F) := by
  rw [← supportProjection_eq_prefixReduce Q F hF]
  exact relativeCCC_iff_projected Q

theorem relativeCCC_of_prepared_continuous_small_limit
    {I : Type} [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    {Nt : I → Type} (Q : ValuedPoset PreparedBA N)
    (Qp : ∀ i,ValuedPoset PreparedBA (Nt i))
    (T : CompleteStageTower (totalBaseMap Q) (fun i => TotalBA (Qp i)))
    (hT : ContinuousStageTower T) (hI : Cardinal.mk I ≤ 𝔠)
    (hMap : ∀ i b,(T.base i).toFun b = baseEmbed (Qp i) b)
    (hCCC : ∀ i,ForcesRelativeCCC (Qp i)) :
    ForcesRelativeCCC Q := by
  apply (relativeCCC_iff_prefixReduce Q (totalBaseMap Q) (fun _ => rfl)).2
  exact projectedCCC_of_prepared_small_continuousTower (totalBaseMap Q) T hT hI
    (fun i => (relativeCCC_iff_prefixReduce (Qp i) (T.base i) (hMap i)).1 (hCCC i))

theorem relativeCCC_of_prepared_checkedKappa_limit
    {Nt : GroundContinuumSuccIndex → Type} (Q : ValuedPoset PreparedBA N)
    (Qp : ∀ i,ValuedPoset PreparedBA (Nt i))
    (T : CompleteStageTower (totalBaseMap Q) (fun i => TotalBA (Qp i)))
    (hMap : ∀ i b,(T.base i).toFun b = baseEmbed (Qp i) b)
    (hCCC : ∀ i,ForcesRelativeCCC (Qp i)) :
    ForcesRelativeCCC Q := by
  apply (relativeCCC_iff_prefixReduce Q (totalBaseMap Q) (fun _ => rfl)).2
  exact projectedCCC_of_checkedKappa_tower prepared_boundsOmegaOne_r432
    actual_prepared_boundsSmallKappa_r473 (totalBaseMap Q) T
    (fun i => (relativeCCC_iff_prefixReduce (Qp i) (T.base i) (hMap i)).1 (hCCC i))

end JSP000930.Negative
