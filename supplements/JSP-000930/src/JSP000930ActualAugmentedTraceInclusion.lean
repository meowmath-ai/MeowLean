import JSP000930ActualAugmentedTestPosets

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

abbrev ActualAugmentedLabel (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :=
  NativeWetzelTrace a × ActualSurvivorLabels a s

noncomputable def actualAugmentedIncludeLabel {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) : ActualAugmentedLabel b s :=
  (actualPrefixIncludeTrace hab p.1,actualSurvivorLabelInclude hab s p.2)

theorem actualAugmentedAdmissible_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (p : NativeWetzelTrace a) (x : TotalBA (actualPrefixQ a)) :
    augmentedAdmissible (actualPrefixQ b) (actualPrefixIncludeTrace hab p)
      ((actualPrefixQuotientShift hab).toFun x) =
      augmentedAdmissible (actualPrefixQ a) p x := by
  unfold augmentedAdmissible
  rw [← actualPrefixQuotientShift_trace hab,← (actualPrefixQuotientShift hab).map_compl,
    ← (actualPrefixQuotientShift hab).map_inf,actualPrefixQuotientShift_support]

theorem actualAugmented_valid_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) :
    (actualAugmentedQ b s).valid (actualAugmentedIncludeLabel hab s p) = (actualAugmentedQ a s).valid p := by
  change (actualPrefixQ b).valid (actualPrefixIncludeTrace hab p.1) ⊓
      augmentedAdmissible (actualPrefixQ b) (actualPrefixIncludeTrace hab p.1)
        ((normalizedSurvivorQ b s).valid (actualSurvivorLabelInclude hab s p.2)) = _
  rw [actualPrefixIncludeTrace_valid,← actualSurvivor_valid_transport hab,actualAugmentedAdmissible_transport] <;> rfl

theorem actualAugmented_refines_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p q : ActualAugmentedLabel a s) :
    (actualAugmentedQ b s).refines (actualAugmentedIncludeLabel hab s p)
      (actualAugmentedIncludeLabel hab s q) = (actualAugmentedQ a s).refines p q := by
  change ((actualAugmentedQ b s).valid (actualAugmentedIncludeLabel hab s p) ⊓
    (actualAugmentedQ b s).valid (actualAugmentedIncludeLabel hab s q)) ⊓
    ((actualPrefixQ b).refines (actualPrefixIncludeTrace hab p.1) (actualPrefixIncludeTrace hab q.1) ⊓
      augmentedAdmissible (actualPrefixQ b) (actualPrefixIncludeTrace hab p.1)
        ((normalizedSurvivorQ b s).refines (actualSurvivorLabelInclude hab s p.2)
          (actualSurvivorLabelInclude hab s q.2))) = _
  rw [actualAugmented_valid_transport,actualAugmented_valid_transport,actualPrefixIncludeTrace_refines,
    ← actualSurvivor_refines_transport hab,actualAugmentedAdmissible_transport] <;> rfl

noncomputable def actualAugmentedInclude {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p : TotalCondition (actualAugmentedQ a s)) :
    TotalCondition (actualAugmentedQ b s) :=
  ⟨p.mask,actualAugmentedIncludeLabel hab s p.trace,p.nonzero,
    p.valid.trans_eq (actualAugmented_valid_transport hab s p.trace).symm⟩

theorem actualAugmentedInclude_mono {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) : Monotone (actualAugmentedInclude hab s) := by
  intro p q h
  exact ⟨h.1,h.2.trans_eq (actualAugmented_refines_transport hab s p.trace q.trace).symm⟩

theorem actualAugmentedIncludeLabel_comp {a b c : GroundContinuumSuccIndex} (hab : a≤b) (hbc : b≤c)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) :
    actualAugmentedIncludeLabel hbc s (actualAugmentedIncludeLabel hab s p) =
      actualAugmentedIncludeLabel (hab.trans hbc) s p := by
  apply Prod.ext
  · exact RawTail.extTrace rfl
  · funext r
    exact Subtype.ext rfl

theorem actualAugmentedIncludeLabel_id (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) :
    actualAugmentedIncludeLabel (le_refl a) s p = p := by
  apply Prod.ext
  · exact RawTail.extTrace rfl
  · funext r
    exact Subtype.ext rfl

theorem actualAugmented_common_forward {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (s : Finset GroundContinuumSuccIndex) (p q : ActualAugmentedLabel a s) :
    commonRefinementValue (actualAugmentedQ a s) p q ≤
      commonRefinementValue (actualAugmentedQ b s)
        (actualAugmentedIncludeLabel hab s p) (actualAugmentedIncludeLabel hab s q) := by
  unfold commonRefinementValue
  apply iSup_le
  intro r
  apply le_iSup_of_le (actualAugmentedIncludeLabel hab s r)
  simp only [actualAugmented_refines_transport,le_rfl]

end JSP000930.Negative
