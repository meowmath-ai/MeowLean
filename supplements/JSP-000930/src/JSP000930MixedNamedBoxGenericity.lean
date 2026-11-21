import JSP000930MixedCohenWordVectors
import JSP000930RationalDyadicBoxes
import JSP000930RationalIntervalCohenNames

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Dyadic JSP000930.Positive.Cohen JSP000930.BooleanAnalysis
open JSP000933.ForcingTransport

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedBoxValue (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (F : Finset I) (s : {i : I // i ∈ F} → Interval) (w : WordVector F) :
    CohenBA B (I × ℕ) :=
  ⨅ i : {i : I // i ∈ F},
    ((⨅ q : RatPresentation, ⨅ (_ : q.value < ((s i).follow (w i)).left),
        intervalCutBits (B := B) i.1 (s i) q) ⊓
      (⨅ q : RatPresentation, ⨅ (_ : ((s i).follow (w i)).right ≤ q.value),
        (intervalCutBits (B := B) i.1 (s i) q)ᶜ))

theorem wordVector_le_namedBox (F : Finset I)
    (s : {i : I // i ∈ F} → Interval) (w : WordVector F) :
    wordVectorValue B F w ≤ namedBoxValue B F s w := by
  apply le_iInf
  intro i
  have h : wordVectorValue B F w ≤ wordValue B i.1 (w i) := iInf_le _ i
  apply le_inf
  · exact le_iInf (fun q => le_iInf (fun hq =>
      h.trans (intervalCut_below_left i.1 (s i) (w i) q hq)))
  · exact le_iInf (fun q => le_iInf (fun hq =>
      h.trans (intervalCut_above_right i.1 (s i) (w i) q hq)))

theorem mixed_Cohen_vector_meets_named_boxes
    (S : Set (I × ℕ)) (F : Finset I) (hFresh : ∀ i ∈ F, ∀ n, (i,n) ∉ S)
    (s : {i : I // i ∈ F} → Interval)
    (p : CohenBlockBA B S) (D : WordVector F → CohenBlockBA B S)
    (hD : ∀ u, p ≤ ⨆ v, D (vectorAppend u v)) :
    blockEmbed B S p ≤ ⨆ w, namedBoxValue B F s w ⊓ blockEmbed B S (D w) := by
  apply (fresh_vector_meets_mixed_dense_words S F hFresh p D hD).trans
  refine iSup_le fun w => le_iSup_of_le w ?_
  exact inf_le_inf (wordVector_le_namedBox F s w) le_rfl

open scoped Classical in
noncomputable def groundOpenCode (S : Set (I × ℕ)) (F : Finset I)
    (s : {i : I // i ∈ F} → Interval) (U : Set ({i : I // i ∈ F} → ℝ))
    (w : WordVector F) : CohenBlockBA B S :=
  if dyadicClosedBox (fun i => (s i).follow (w i)) ⊆ U then ⊤ else ⊥

theorem groundOpenCode_dense (S : Set (I × ℕ)) (F : Finset I)
    (s : {i : I // i ∈ F} → Interval) (U : Set ({i : I // i ∈ F} → ℝ))
    (hU : IsOpen U) (hDense : Dense U) (u : WordVector F) :
    (⊤ : CohenBlockBA B S) ≤ ⨆ v, groundOpenCode (B := B) S F s U (vectorAppend u v) := by
  classical
  obtain ⟨v, hv⟩ := exists_vector_append_box_subset s u hU hDense
  refine le_iSup_of_le v ?_
  change (⊤ : CohenBlockBA B S) ≤
    groundOpenCode (B := B) S F s U (vectorAppend u v)
  have h : dyadicClosedBox (fun i => (s i).follow ((vectorAppend u v) i)) ⊆ U := hv
  simp only [groundOpenCode, ite_eq_left h, le_rfl]

end JSP000930.Negative.Cohen
