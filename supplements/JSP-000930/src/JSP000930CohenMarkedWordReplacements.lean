import JSP000930MixedNamedBoxGenericity
import JSP000933MarkedBaseEmbedding

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Cohen JSP000930.Positive.Dyadic JSP000933.MarkedForcing
open JSP000933.BooleanCompletion

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem cohen_append_on_earlier_mark
    (t : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbT : b ≤ t.mask)
    (F : Finset I) (v : I → List Bool) :
    ∃ q : CohenTotal B (I × ℕ), q ≤ t ∧ q.mask = b ∧
      ∀ i ∈ F,WordMatches q.trace i (completeRowWord t.trace i ++ v i) := by
  obtain ⟨s,hs,hW,_⟩ := exists_refine_vector_only_rows t.trace F v
  let q : CohenTotal B (I × ℕ) := ⟨b,s,hb,le_top⟩
  exact ⟨q,(cohen_total_le_iff _ _).mpr ⟨hbT,hs⟩,rfl,hW⟩

theorem cohen_boxes_and_base_refine_together
    (t : CohenTotal B (I × ℕ)) (b : B) (hb : b ≠ ⊥) (hbT : b ≤ t.mask)
    (F : Finset I) (s : {i : I // i ∈ F} → Interval) (v : I → List Bool) :
    ∃ q : CohenTotal B (I × ℕ), q ≤ t ∧ q.mask = b ∧
      imageCondition q ≤ baseEmbed (valuedCohen B (I × ℕ)) b ⊓
        namedBoxValue B F s (fun i => completeRowWord t.trace i.1 ++ v i.1) := by
  obtain ⟨q,hqt,hqB,hW⟩ := cohen_append_on_earlier_mark t b hb hbT F v
  refine ⟨q,hqt,hqB,le_inf ?_ ?_⟩
  · apply (baseEmbed_reflects_mask_r427 q b).mpr
    exact hqB.le
  · have hWord : imageCondition q ≤ wordVectorValue B F
        (fun i => completeRowWord t.trace i.1 ++ v i.1) := by
      apply le_iInf
      intro i
      exact image_le_wordValue q i.1 _ (hW i.1 i.2)
    exact hWord.trans (wordVector_le_namedBox F s _)

end JSP000930.Negative.Cohen
