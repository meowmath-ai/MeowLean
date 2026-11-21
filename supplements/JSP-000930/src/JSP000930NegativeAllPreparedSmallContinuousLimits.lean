import JSP000930NegativeActualMixedOmegaOneRelativeLimitCCC
import JSP000933PreparedSmallTraceEnum
import JSP000933PreparedPrefixCHRealCodes
import JSP000933PreparedProduct

open Cardinal

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.ForcingTransport JSP000933.PreparedModel

variable {B D I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable [LinearOrder I] {A : I → Type} [∀ t,CompleteBooleanAlgebra (A t)]

theorem projectedCCC_of_cofinal_countable_stages (hB : BoundsCountableOmegaOneNames B)
    (F : CompleteValueMap B D) (T : CompleteStageTower F A)
    (f : ℕ → I) (hf : ∀ i,∃ n,i ≤ f n)
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  letI : ∀ n : ℕ,CompleteBooleanAlgebra (A (f n)) := fun _ => inferInstance
  apply projectedCCC_of_countable_dense_union hB
    (fun n => T.stage (f n)) (prefixReduce F) (fun n => prefixReduce (T.base (f n)))
    (fun f => (prefixReduce_gc F).l_iSup (f := f)) (fun n a => T.project_base (f n) a) (fun n => hCCC (f n))
  intro x hx
  obtain ⟨i,a,ha,hAx⟩ := T.final_dense x hx
  obtain ⟨n,hn⟩ := hf i
  refine ⟨n,(T.shift i (f n) hn).toFun a,?_,?_⟩
  · simpa only [T.shift_coherent] using ha
  · simpa only [T.shift_coherent] using hAx

theorem projectedCCC_of_prepared_small_continuousTower
    [WellFoundedLT I] [Nonempty I]
    (F : CompleteValueMap PreparedBA D) (T : CompleteStageTower F A)
    (hT : ContinuousStageTower T) (hI : Cardinal.mk I ≤ 𝔠)
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  by_cases hω : AllCountableGroundBounded I
  · obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471 I hI
    exact projectedCCC_of_mixedOmegaOne_prepared_limit preparedProduct_countablyClosed_r401
      prepared_boundsOmegaOne_r432 F T hT hω E hCCC
  · have hex : ∃ f : ℕ → I,¬ ∃ b,∀ n,f n < b := by
      by_contra hn
      apply hω
      intro f
      by_contra h
      exact hn ⟨f,h⟩
    obtain ⟨f,hf⟩ := hex
    apply projectedCCC_of_cofinal_countable_stages prepared_boundsOmegaOne_r432 F T f ?_ hCCC
    intro a
    by_contra hn
    apply hf
    exact ⟨a,fun n => lt_of_not_ge (fun h => hn ⟨n,h⟩)⟩

end JSP000930.Negative
