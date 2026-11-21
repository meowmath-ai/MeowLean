import JSP000930NativeWetzelFinalSiteCover

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem castDensePullBase930 {D N P : Type} [CompleteBooleanAlgebra D] [Preorder P]
    (Q R : ValuedPoset D N) (h : Q = R)
    (F : DenseForcingMap P (TotalCondition Q)) (b : D) :
    ((h ▸ F : DenseForcingMap P (TotalCondition R)).pullIso) (baseEmbed R b) =
      F.pullIso (baseEmbed Q b) := by
  cases h
  rfl

structure WetzelWorkInputs (B : Type) [NontrivialCompleteBooleanAlgebra B] where
  site : GroundContinuumSuccIndex → ComplexBits B
  palette : GroundContinuumSuccIndex → ℕ → ComplexBits B

abbrev WorkingDomain (a : GroundContinuumSuccIndex) (j : GroundContinuumSuccIndex) : Prop := j<a

noncomputable def WetzelWorkInputs.row (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :=
  supportedSymbolicQ W.site W.palette (WorkingDomain a)

noncomputable def WetzelWorkInputs.stage (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :=
  wetzelTaggedWork W.site W.palette (WorkingDomain a)

abbrev WetzelWorkCohenAlgebra (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :=
  StageCohenBA (TotalBA (W.row a))

noncomputable def WetzelWorkInputs.oldToCohen (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :
    CompleteValueMap B (WetzelWorkCohenAlgebra W a) :=
  composeCompleteValueMaps (markedCompleteValueMap (W.row a)) (stageCohenMap _)

noncomputable def WetzelWorkInputs.comparison (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :
    DenseForcingMap (TotalCondition (W.stage a))
      (TotalCondition (valuedCohen (TotalBA (W.row a)) WorkCohenCoordinate)) :=
  denseForcingMap_comp930 (wetzelWorkTagDense W.site W.palette (WorkingDomain a))
    (analyticThenCohenDenseMap (W.row a) WorkCohenCoordinate)

noncomputable def WetzelWorkInputs.cohenToStage (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex) :
    CompleteValueMap (WetzelWorkCohenAlgebra W a) (TotalBA (W.stage a)) :=
  completeMapOfDensePull930 (W.comparison a)

theorem WetzelWorkInputs.cohenToStage_base (W : WetzelWorkInputs B) (a : GroundContinuumSuccIndex)
    (b : B) :
    (W.cohenToStage a).toFun ((W.oldToCohen a).toFun b) = baseEmbed (W.stage a) b := by
  unfold WetzelWorkInputs.cohenToStage WetzelWorkInputs.comparison WetzelWorkInputs.stage
  rw [completeMapOfDensePull930_apply]
  apply (densePull_comp930 (wetzelWorkTagDense W.site W.palette (WorkingDomain a))
    (analyticThenCohenDenseMap (W.row a) WorkCohenCoordinate) ((W.oldToCohen a).toFun b)).trans
  let P := W.row a
  let Q := valuedCohen B WorkCohenCoordinate
  let D := pairIteratedDenseMap P Q
  have he : (analyticThenCohenDenseMap P WorkCohenCoordinate).pullIso
      ((W.oldToCohen a).toFun b) = baseEmbed (valuedPair P Q) b := by
    unfold analyticThenCohenDenseMap
    have hQ : changeValuedBase (markedCompleteValueMap P) Q =
        valuedCohen (TotalBA P) WorkCohenCoordinate :=
      change_valuedCohen (markedCompleteValueMap P) WorkCohenCoordinate
    have hBase : (W.oldToCohen a).toFun b =
        baseEmbed (valuedCohen (TotalBA P) WorkCohenCoordinate) (baseEmbed P b) := rfl
    rw [hBase]
    change (hQ ▸ D : DenseForcingMap (TotalCondition (valuedPair P Q))
      (TotalCondition (valuedCohen (TotalBA P) WorkCohenCoordinate))).pullIso
        (baseEmbed (valuedCohen (TotalBA P) WorkCohenCoordinate) (baseEmbed P b)) = _
    rw [castDensePullBase930]
    exact pairIteratedDenseMap_base P Q b
  change (wetzelWorkTagDense W.site W.palette (WorkingDomain a)).pullIso
    ((analyticThenCohenDenseMap P WorkCohenCoordinate).pullIso ((W.oldToCohen a).toFun b)) = _
  rw [he]
  exact taggedDenseMap_base (wetzelRawWork W.site W.palette (WorkingDomain a))
    (decodeWork (WorkingDomain a)) .zero rfl (fun v => .work v.1.val v.2) _ b

end JSP000930.Negative
