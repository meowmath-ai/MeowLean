import JSP000930HistoricalCertifiedStage

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing JSP000933.PreparedModel

variable {A B N : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
variable [NontrivialCompleteBooleanAlgebra B] {a b : A}

theorem historicalAdmission_of_native
    (tail : BasedTailPolicy A B (CertifiedStageLabel N)) (ha : a ≠ ⊥) (hab : a < b)
    (Q : ValuedPoset (PreStageAlgebra tail (a := a)) N)
    (hQ : TailStageValues tail (a := a) = CertifiedStageLabel.admits Q) :
    HistoricalAdmission (earlierValidated (basedPolicy tail) b) hab Q := by
  classical
  intro p s
  change localStageValid (basedPolicy tail) a p.trace s ↔ _
  rw [localStageValid_unfold_r85]
  have hRaw : rawProjection (earlierValidated (basedPolicy tail) a) p.trace = imageCondition p :=
    rawProjection_of_good_r84 _ p
  change rawProjection (earlierValidated (basedPolicy tail) a) p.trace ≤
      basedPolicy tail a (earlierValidated (basedPolicy tail) a) s ↔ _
  rw [hRaw]
  by_cases h : s.1 = ⊤
  · simp only [basedPolicy,ite_eq_right ha,ite_eq_left h,h,true_and]
    change imageCondition p ≤ TailStageValues tail (a := a) s.2 ↔ _
    rw [hQ] <;> rfl
  · simp only [basedPolicy,ite_eq_right ha,ite_eq_right h,h,false_and]
    exact ⟨fun he => imageCondition_ne_bot_r50 p (le_bot_iff.mp he),False.elim⟩

noncomputable def embedHistoricalIterand (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) : CompleteValueMap (TotalBA Q) (RO (GoodPrefix old)) :=
  completeMapOfDensePull930 (historicalStageComparison old hab hP succ Q hQ)

theorem embedHistoricalIterand_base (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N) (hQ : HistoricalAdmission old hab Q)
    (u : HistoryPrefixAlgebra old hab.le) :
    (embedHistoricalIterand old hab hP succ Q hQ).toFun (baseEmbed Q u) =
      (historyCompleteEmbed hab.le old hP).toFun u := by
  let D := historicalStageComparison old hab hP succ Q hQ
  change D.pullIso (baseEmbed Q u) = (historyCompleteEmbed hab.le old hP).toFun u
  have hTest (p : GoodPrefix old) :
      imageCondition p ≤ D.pullIso (baseEmbed Q u) ↔
        imageCondition p ≤ (historyCompleteEmbed hab.le old hP).toFun u := by
    rw [image_le_iff_member,image_le_historyCompleteEmbed]
    change D.map p ∈ (baseEmbed Q u : LowerSet (TotalCondition Q)) ↔ _
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (hTest p).mp))
    (le_of_image_tests (fun p => (hTest p).mpr))

end JSP000930.Negative
