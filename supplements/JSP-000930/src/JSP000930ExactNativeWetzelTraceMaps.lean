import JSP000930RelativeAugmentedSurvivorCCC

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

abbrev NativeWetzelTrace (a : GroundContinuumSuccIndex) :=
  PrefixTail (wetzelWorkStage a) WetzelCertifiedLabel

noncomputable def actualPrefixQ (a : GroundContinuumSuccIndex) :=
  nativeWetzelPrefixQ actualWetzelRest (wetzel_bot_lt_work a)

noncomputable def actualPrefixQuotientShift {a b : GroundContinuumSuccIndex} (hab : a≤b) :
    CompleteValueMap (TotalBA (actualPrefixQ a)) (TotalBA (actualPrefixQ b)) :=
  wetzelPrefixToPrefix actualWetzelRest (wetzel_bot_lt_work a)
    ((wetzelWorkStage_le_iff _ _).mpr hab)

noncomputable def actualPrefixIncludeTrace {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p : NativeWetzelTrace a) : NativeWetzelTrace b :=
  includeRawTail (fun _ hj => hj.trans_le ((wetzelWorkStage_le_iff _ _).mpr hab)) p

theorem actualPrefixIncludeTrace_order {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p q : NativeWetzelTrace a) :
    actualPrefixIncludeTrace hab p ≤ actualPrefixIncludeTrace hab q ↔ p≤q :=
  Iff.rfl

theorem actualPrefixQuotientShift_base {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (m : PreparedBA) :
    (actualPrefixQuotientShift hab).toFun (baseEmbed (actualPrefixQ a) m) =
      baseEmbed (actualPrefixQ b) m :=
  wetzelPrefixToPrefix_base actualWetzelRest _ _ m

theorem actualPrefixQuotientShift_trace {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p : NativeWetzelTrace a) :
    (actualPrefixQuotientShift hab).toFun (traceValue (actualPrefixQ a) p) =
      traceValue (actualPrefixQ b) (actualPrefixIncludeTrace hab p) := by
  let E := nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work b)
  apply E.injective
  change E (E.symm ((prefixReduction ((wetzelWorkStage_le_iff _ _).mpr hab)).boolPullback
    ((nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work a)) (traceValue (actualPrefixQ a) p)))) = _
  rw [E.apply_symm_apply]
  exact earlier_to_later_traceValue actualWetzelTail (wetzel_bot_lt_work a)
    ((wetzelWorkStage_le_iff _ _).mpr hab) p

theorem actualPrefixQuotientShift_rectangle {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p : NativeWetzelTrace a) (m : PreparedBA) :
    (actualPrefixQuotientShift hab).toFun (traceRectangle (actualPrefixQ a) p m) =
      traceRectangle (actualPrefixQ b) (actualPrefixIncludeTrace hab p) m := by
  simp only [traceRectangle,(actualPrefixQuotientShift hab).map_inf,
    actualPrefixQuotientShift_base,actualPrefixQuotientShift_trace]

theorem actualPrefixQuotientShift_support {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (x : TotalBA (actualPrefixQ a)) :
    supportProjection (actualPrefixQ b) ((actualPrefixQuotientShift hab).toFun x) =
      supportProjection (actualPrefixQ a) x := by
  let F := actualPrefixQuotientShift hab
  have h (m : PreparedBA) :
      supportProjection (actualPrefixQ b) (F.toFun x) ≤ m ↔ supportProjection (actualPrefixQ a) x ≤ m := by
    rw [supportProjection_le_iff_r428,supportProjection_le_iff_r428,← actualPrefixQuotientShift_base hab]
    exact ⟨F.reflect_le_r93,fun hx => F.monotone hx⟩
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

theorem actualPrefixIncludeTrace_valid {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p : NativeWetzelTrace a) :
    (actualPrefixQ b).valid (actualPrefixIncludeTrace hab p) = (actualPrefixQ a).valid p := by
  calc
    _ = supportProjection (actualPrefixQ b) (traceValue (actualPrefixQ b) (actualPrefixIncludeTrace hab p)) :=
      (traceValue_support_r429 _ _).symm
    _ = _ := by
      rw [← actualPrefixQuotientShift_trace hab,actualPrefixQuotientShift_support,traceValue_support_r429]

theorem actualPrefixIncludeTrace_refines {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p q : NativeWetzelTrace a) :
    (actualPrefixQ b).refines (actualPrefixIncludeTrace hab p) (actualPrefixIncludeTrace hab q) =
      (actualPrefixQ a).refines p q := by
  classical
  change (if actualPrefixIncludeTrace hab p ≤ actualPrefixIncludeTrace hab q then
       (actualPrefixQ b).valid (actualPrefixIncludeTrace hab p) ⊓
       (actualPrefixQ b).valid (actualPrefixIncludeTrace hab q) else ⊥) =
    (if p≤q then (actualPrefixQ a).valid p ⊓ (actualPrefixQ a).valid q else ⊥)
  simp only [actualPrefixIncludeTrace_order,actualPrefixIncludeTrace_valid]

end JSP000930.Negative
