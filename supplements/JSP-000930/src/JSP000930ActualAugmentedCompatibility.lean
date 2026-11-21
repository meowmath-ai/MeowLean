import JSP000930ActualCountableJointLimit

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

theorem common_changeValuedBase930 {B C N : Type} [CompleteBooleanAlgebra B]
    [CompleteBooleanAlgebra C] (F : CompleteValueMap B C)
    (Q : ValuedPoset B N) (p q : N) :
    F.toFun (commonRefinementValue Q p q) =
      commonRefinementValue (changeValuedBase F Q) p q := by
  simp only [commonRefinementValue,F.map_iSup,F.map_inf] <;> rfl

theorem actualSurvivor_common_transport {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (hB : ∀ j<b,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (p q : ActualSurvivorLabels a s) :
    (actualPrefixQuotientShift hab).toFun (commonRefinementValue (normalizedSurvivorQ a s) p q) =
      commonRefinementValue (normalizedSurvivorQ b s)
        (actualSurvivorLabelInclude hab s p) (actualSurvivorLabelInclude hab s q) := by
  classical
  unfold normalizedSurvivorQ
  rw [← common_changeValuedBase930,← common_changeValuedBase930]
  change (actualPrefixQuotientShift hab).toFun
      (actualPrefixHistoryIso a (commonRefinementValue (actualSurvivorProduct a s) p q)) =
    actualPrefixHistoryIso b (commonRefinementValue (actualSurvivorProduct b s)
      (actualSurvivorLabelInclude hab s p) (actualSurvivorLabelInclude hab s q))
  rw [actualPrefixHistoryIso_shift]
  apply congrArg (actualPrefixHistoryIso b)
  unfold actualSurvivorProduct
  rw [rowProduct_commonRefinement_eq,rowProduct_commonRefinement_eq,(actualHistoryShift hab).map_iInf]
  apply iInf_congr
  intro r
  exact map_supported_commonRefinement (fun _ hj => hj.trans_le hab) (actualHistoryShift hab)
    _ _ _ _
    (fun _ hj => actualWorkingSite_transport hab hj)
    (fun _ hj n => actualWetzelRowPalette_transport hab hj r.val n)
    (fun j _ => actualWorkingSite_proper b j)
    (fun j _ => actualWetzelRowPalette_proper b r.val j)
    (fun _ hj _ hi hne => by
      rw [actualWorkingSite_supportApart b hB (hj.trans_le hab) (hi.trans_le hab) hne,compl_bot] <;> exact le_rfl)
    (p r) (q r)

theorem actualAugmentedDense_basicMask {a : GroundContinuumSuccIndex}
    (s : Finset GroundContinuumSuccIndex) (p : TotalCondition (actualAugmentedQ a s)) :
    ((augmentedDenseMap (actualPrefixQ a) (normalizedSurvivorQ a s)).map p).mask =
      traceRectangle (actualPrefixQ a) p.trace.1 p.mask := by
  exact (augmented_rectangle_image (actualPrefixQ a) p.trace.1 p.nonzero
    (p.valid.trans inf_le_left)).symm

theorem actualAugmentedDense_compat_reflect {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (hB : ∀ j<b,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) {p q : TotalCondition (actualAugmentedQ a s)}
    (h : Compatible (actualAugmentedInclude hab s p) (actualAugmentedInclude hab s q)) :
    Compatible p q := by
  let D := augmentedDenseMap (actualPrefixQ a) (normalizedSurvivorQ a s)
  let E := augmentedDenseMap (actualPrefixQ b) (normalizedSurvivorQ b s)
  let F := actualPrefixQuotientShift hab
  have h' : Compatible (E.map (actualAugmentedInclude hab s p)) (E.map (actualAugmentedInclude hab s q)) := by
    obtain ⟨r,hrp,hrq⟩ := h
    exact ⟨E.map r,E.monotone hrp,E.monotone hrq⟩
  apply D.reflect_compatible
  apply (totalCompatible_iff_r426 _ _).mpr
  have hN := (totalCompatible_iff_r426 _ _).mp h'
  rw [actualAugmentedDense_basicMask s,actualAugmentedDense_basicMask s] at hN ⊢
  change ((traceRectangle (actualPrefixQ b) (actualPrefixIncludeTrace hab p.trace.1) p.mask ⊓
    traceRectangle (actualPrefixQ b) (actualPrefixIncludeTrace hab q.trace.1) q.mask) ⊓
    commonRefinementValue (normalizedSurvivorQ b s)
      (actualSurvivorLabelInclude hab s p.trace.2) (actualSurvivorLabelInclude hab s q.trace.2)) ≠ ⊥ at hN
  rw [← actualPrefixQuotientShift_rectangle hab,← actualPrefixQuotientShift_rectangle hab,
    ← actualSurvivor_common_transport hab hB,← F.map_inf,← F.map_inf,← F.map_bot] at hN
  exact fun he => hN (congrArg F.toFun he)

theorem actualAugmented_common_backward {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (hB : ∀ j<b,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (p q : ActualAugmentedLabel a s) :
    commonRefinementValue (actualAugmentedQ b s)
        (actualAugmentedIncludeLabel hab s p) (actualAugmentedIncludeLabel hab s q) ≤
      commonRefinementValue (actualAugmentedQ a s) p q := by
  let n := commonRefinementValue (actualAugmentedQ b s)
    (actualAugmentedIncludeLabel hab s p) (actualAugmentedIncludeLabel hab s q)
  let l := commonRefinementValue (actualAugmentedQ a s) p q
  change n≤l
  by_contra hn
  let m := n ⊓ lᶜ
  have hm : m ≠ ⊥ := fun h => hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr h.le))
  have hV := commonRefinementValue_forcesValid_r426 (actualAugmentedQ b s)
    (actualAugmentedIncludeLabel hab s p) (actualAugmentedIncludeLabel hab s q)
  rw [actualAugmented_valid_transport,actualAugmented_valid_transport] at hV
  let u : TotalCondition (actualAugmentedQ a s) := ⟨m,p,hm,(inf_le_left.trans hV).trans inf_le_left⟩
  let v : TotalCondition (actualAugmentedQ a s) := ⟨m,q,hm,(inf_le_left.trans hV).trans inf_le_right⟩
  have hNew : Compatible (actualAugmentedInclude hab s u) (actualAugmentedInclude hab s v) := by
    apply (totalCompatible_iff_r426 _ _).mpr
    change (m ⊓ m) ⊓ n ≠ ⊥
    rwa [inf_idem,inf_eq_left.mpr (show m≤n from inf_le_left)]
  have hOld := (totalCompatible_iff_r426 _ _).mp (actualAugmentedDense_compat_reflect hab hB s hNew)
  change (m ⊓ m) ⊓ l ≠ ⊥ at hOld
  rw [inf_idem] at hOld
  exact hOld (disjoint_iff_inf_le.mp (disjoint_compl_left.mono_left (show m≤lᶜ from inf_le_right)) |> le_bot_iff.mp)

end JSP000930.Negative
