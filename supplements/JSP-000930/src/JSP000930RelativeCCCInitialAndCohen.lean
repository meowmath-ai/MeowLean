import JSP000930RelativeCCCCohenProduct
import JSP000930SymbolicTraceCardinality

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.ForcingTransport

variable {B X N : Type} [NontrivialCompleteBooleanAlgebra B]

theorem relativeCCC_after_cohen (hB : BoundsCountableOmegaOneNames B)
    (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q) :
    ForcesRelativeCCC (changeValuedBase (markedCompleteValueMap (valuedCohen B X)) Q) :=
  relativeCCC_after_left_of_product (valuedCohen B X) Q (relativeCCC_cohen_pair hB Q hQ)

theorem relativeCCC_countable_carrier [Countable N]
    (hB : BoundsCountableOmegaOneNames B) (Q : ValuedPoset B N) :
    ForcesRelativeCCC Q := by
  classical
  intro W hW hWD
  letI := Encodable.ofCountable N
  let e : ℕ → N := fun i => (Encodable.decode i).getD Q.weakest
  have hSurj : Function.Surjective e := by
    intro n
    refine ⟨Encodable.encode n,?_⟩
    simp [e,Encodable.encodek]
  have hEach (n : N) : unboundedValue (fun i => W i n) = ⊥ := by
    apply le_bot_iff.mp
    apply (unboundedValue_le_pairOverlap_r431 _).trans
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    have hC : Q.valid n ≤ commonRefinementValue Q n n :=
      le_iSup_of_le n (le_inf (Q.refl n) (Q.refl n))
    have hN : W i n ⊓ W j.val n ≤ commonRefinementValue Q n n :=
      inf_le_left.trans ((hW i n).trans hC)
    exact (le_inf le_rfl hN).trans_eq (hWD i j.val j.2 n n)
  have hAll (i : OmegaOneIndex) : (⨆ n : N,W i n) = ⨆ k : ℕ,W i (e k) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      obtain ⟨k,rfl⟩ := hSurj n
      exact le_iSup (fun k => W i (e k)) k
    · exact iSup_le (fun k => le_iSup (W i) (e k))
  simp only [hAll, unboundedValue_countablePartition_r433 hB, hEach, iSup_bot]

end JSP000930.Negative
