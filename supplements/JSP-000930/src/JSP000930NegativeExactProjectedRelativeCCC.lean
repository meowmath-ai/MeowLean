import JSP000930NegativeActualBooleanPrefixReductions
import JSP000933RelativeTraceEnumeration
import JSP000933NativeBasePrefixCoherence

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem marked_projection_bot (Q : ValuedPoset B N) :
    supportProjection Q ⊥ = ⊥ :=
  le_bot_iff.mp ((supportProjection_le_iff_r428 Q _ _).2 bot_le)

theorem traceRectangle_projection (Q : ValuedPoset B N) (t : N) (b : B) :
    supportProjection Q (traceRectangle Q t b) = Q.valid t ⊓ b := by
  rw [traceRectangle,inf_comm,supportProjection_meet_base_r428,traceValue_support_r429]

theorem actual_traceRectangle_cover (Q : ValuedPoset B N) (x : TotalBA Q) :
    x = ⨆ t,traceRectangle Q t (Q.valid t ⊓ traceAccept Q x t) := by
  apply le_antisymm _ (iSup_le fun t =>
    (traceRectangle_accept_iff_r464 Q x t _).2 inf_le_right)
  apply JSP000933.ForcingTransport.le_of_image_tests
  intro r hr
  have hImage : imageCondition r = traceRectangle Q r.trace r.mask :=
    image_eq_base_meet_trace_r429 r
  have ha : r.mask ≤ traceAccept Q x r.trace :=
    (traceRectangle_accept_iff_r464 Q x r.trace _).1 (hImage.ge.trans hr)
  rw [hImage]
  exact le_iSup_of_le r.trace ((traceRectangle_mono_r464 Q r.trace)
    (le_inf r.valid ha))

theorem relativeCCC_iff_projected (Q : ValuedPoset B N) :
    ForcesRelativeCCC Q ↔ ProjectedAntichainCCC (supportProjection Q) := by
  constructor
  · intro h x hX
    let W (i : OmegaOneIndex) (t : N) := Q.valid t ⊓ traceAccept Q (x i) t
    have hValid (i : OmegaOneIndex) (t : N) : W i t ≤ Q.valid t := inf_le_left
    have hSep (i j : OmegaOneIndex) (hij : i < j) (t u : N) :
        (W i t ⊓ W j u) ⊓ commonRefinementValue Q t u = ⊥ := by
      have hLeft := (traceRectangle_accept_iff_r464 Q (x i) t (W i t)).2 inf_le_right
      have hRight := (traceRectangle_accept_iff_r464 Q (x j) u (W j u)).2 inf_le_right
      have he := ((hX i j hij).mono hLeft hRight).eq_bot
      rw [inf_comm,← traceRectangle_pair_support_r464 Q t u (W i t) (W j u),he,
        marked_projection_bot]
    have hProj (i : OmegaOneIndex) : supportProjection Q (x i) = ⨆ t,W i t := by
      rw [actual_traceRectangle_cover Q (x i),(supportProjection_gc_r428 Q).l_iSup]
      apply iSup_congr
      intro t
      rw [traceRectangle_projection,inf_eq_right.mpr (hValid i t)]
    simpa only [hProj] using h W hValid hSep
  · intro h W hValid hSep
    let x (i : OmegaOneIndex) := ⨆ t,traceRectangle Q t (W i t)
    have hX (i j : OmegaOneIndex) (hij : i < j) : Disjoint (x i) (x j) := by
      apply disjoint_iff_inf_le.mpr
      simp only [x,iSup_inf_iSup]
      apply iSup_le
      rintro ⟨t,u⟩
      rw [← baseEmbed_bot_r427 Q]
      apply (supportProjection_le_iff_r428 Q _ _).1
      rw [traceRectangle_pair_support_r464,inf_comm,hSep i j hij t u]
    have hRows (i : OmegaOneIndex) : supportProjection Q (x i) = ⨆ t,W i t := by
      change supportProjection Q (⨆ t, traceRectangle Q t (W i t)) = _
      rw [(supportProjection_gc_r428 Q).l_iSup]
      exact iSup_congr fun t => (traceRectangle_projection Q t (W i t)).trans
        (inf_eq_right.mpr (hValid i t))
    simpa only [hRows] using h x hX

end JSP000930.Negative
