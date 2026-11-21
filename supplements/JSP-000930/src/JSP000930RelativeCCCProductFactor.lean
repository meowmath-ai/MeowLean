import JSP000930JointProjectedTraceWeights

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport JSP000933.OpenGraphForcing

variable {B N K : Type} [NontrivialCompleteBooleanAlgebra B]

theorem relativeCCC_after_left_of_product (P : ValuedPoset B N) (Q : ValuedPoset B K)
    (hPQ : ForcesRelativeCCC (valuedPair P Q)) :
    ForcesRelativeCCC (changeValuedBase (markedCompleteValueMap P) Q) := by
  intro W hValid hDisj
  let V (i : OmegaOneIndex) (a : N × K) : B := traceWeight P (W i a.2) a.1
  have hVValid (i : OmegaOneIndex) (a : N × K) : V i a ≤ (valuedPair P Q).valid a := by
    refine le_inf (traceWeight_le_valid_r434 P _ _) ?_
    have hP : supportProjection P (W i a.2) ≤ Q.valid a.2 :=
      (supportProjection_le_iff_r428 _ _ _).mpr (hValid i a.2)
    rw [← traceWeight_joins_projection_r434] at hP
    exact (le_iSup (traceWeight P (W i a.2)) a.1).trans hP
  have hVDisj (i j : OmegaOneIndex) (hij : i < j) (a b : N × K) :
      (V i a ⊓ V j b) ⊓ commonRefinementValue (valuedPair P Q) a b = ⊥ := by
    apply le_bot_iff.mp
    rw [common_valuedPair,← inf_assoc]
    have hx := hDisj i j hij a.2 b.2
    rw [common_changeValuedBase] at hx
    change (W i a.2 ⊓ W j b.2) ⊓ baseEmbed P (commonRefinementValue Q a.2 b.2) = ⊥ at hx
    have hJ := traceWeights_joint_support P (W i a.2) (W j b.2) a.1 b.1
      (commonRefinementValue Q a.2 b.2)
    exact hJ.trans_eq ((supportProjection_zero_iff_r428 P _).mpr hx)
  have hCCC := hPQ V hVValid hVDisj
  let W₀ (i : OmegaOneIndex) := ⨆ n : K, W i n
  let V₀ (i : OmegaOneIndex) := ⨆ a : N × K, V i a
  have hProjection (i : OmegaOneIndex) : supportProjection P (W₀ i) = V₀ i := by
    unfold W₀ V₀
    rw [supportProjection_iSup930]
    simp only [← traceWeight_joins_projection_r434]
    apply le_antisymm
    · apply iSup_le
      intro n
      apply iSup_le
      intro r
      exact le_iSup (V i) (r,n)
    · apply iSup_le
      rintro ⟨r,n⟩
      exact le_iSup_of_le n (le_iSup (traceWeight P (W i n)) r)
  change unboundedValue W₀ = ⊥
  apply (supportProjection_zero_iff_r428 P _).mp
  apply le_bot_iff.mp
  apply le_trans ?_ (show unboundedValue V₀ ≤ ⊥ from hCCC.le)
  unfold unboundedValue
  apply le_iInf
  intro b
  apply (supportProjection_mono_r428 P (iInf_le (aboveValue W₀) b)).trans
  unfold aboveValue
  rw [supportProjection_iSup930]
  simp only [hProjection,le_rfl]

end JSP000930.Negative
