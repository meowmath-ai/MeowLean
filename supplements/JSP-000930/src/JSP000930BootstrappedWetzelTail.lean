import JSP000930WetzelLabelCardinality
import JSP000933NativeBasePrefixCoherence

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.FiniteSupport
open JSP000933.BooleanCompletion JSP000933.ForcingTransport

abbrev WetzelTailPolicy := BasedTailPolicy WetzelStageIndex PreparedBA WetzelCertifiedLabel

noncomputable def wetzelBootstrapTail (rest : WetzelTailPolicy) : WetzelTailPolicy := by
  classical
  intro i old
  exact if i = wetzelBulkStage then CertifiedStageLabel.admits (wetzelTaggedBulk (B := RO (GoodPrefix old)))
    else rest i old

theorem wetzelBootstrapTail_bulk (rest : WetzelTailPolicy)
    (old : PrefixValidator wetzelBulkStage (BasedLabel PreparedBA WetzelCertifiedLabel)) :
    wetzelBootstrapTail rest wetzelBulkStage old =
      CertifiedStageLabel.admits (wetzelTaggedBulk (B := RO (GoodPrefix old))) := by
  classical
  simp [wetzelBootstrapTail]

theorem wetzelBootstrapTail_work (rest : WetzelTailPolicy) (i : GroundContinuumSuccIndex)
    (old : PrefixValidator (wetzelWorkStage i) (BasedLabel PreparedBA WetzelCertifiedLabel)) :
    wetzelBootstrapTail rest (wetzelWorkStage i) old = rest (wetzelWorkStage i) old := by
  classical
  have h : wetzelWorkStage i ≠ wetzelBulkStage := by
    intro h
    exact WithBot.coe_ne_bot (WithBot.coe_injective h)
  simp only [wetzelBootstrapTail,ite_eq_right h]

theorem wetzelBulkStage_ne_bot : wetzelBulkStage ≠ (⊥ : WetzelStageIndex) :=
  WithBot.coe_ne_bot

theorem wetzelWorkStage_ne_bot (a : GroundContinuumSuccIndex) : wetzelWorkStage a ≠ (⊥ : WetzelStageIndex) :=
  WithBot.coe_ne_bot

theorem wetzelBootstrapStage_monotone (rest : WetzelTailPolicy)
    (h : ∀ a old,Monotone (rest a old)) (a : WetzelStageIndex)
    (old : PrefixValidator a (BasedLabel PreparedBA WetzelCertifiedLabel)) :
    Monotone (wetzelBootstrapTail rest a old) := by
  classical
  unfold wetzelBootstrapTail
  split
  · exact CertifiedStageLabel.admits_mono _
  · exact h a old

theorem wetzelBootstrapStage_top (rest : WetzelTailPolicy)
    (h : ∀ a old,rest a old ⊤ = ⊤) (a : WetzelStageIndex)
    (old : PrefixValidator a (BasedLabel PreparedBA WetzelCertifiedLabel)) :
    wetzelBootstrapTail rest a old ⊤ = ⊤ := by
  classical
  unfold wetzelBootstrapTail
  split
  · exact CertifiedStageLabel.admits_top _
  · exact h a old

end JSP000930.Negative
