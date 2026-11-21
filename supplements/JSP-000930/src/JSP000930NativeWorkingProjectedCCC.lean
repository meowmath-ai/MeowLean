import JSP000930ActualWorkRelativeCCC

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen
open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.FiniteSupport
open JSP000933.PreparedModel

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem wetzelTaggedWork_relativeCCC
    (site : GroundContinuumSuccIndex → ComplexBits B)
    (H : GroundContinuumSuccIndex → ℕ → ComplexBits B) (A : GroundContinuumSuccIndex → Prop)
    (hB : BoundsCountableOmegaOneNames B) (hP : ForcesRelativeCCC (supportedSymbolicQ site H A)) :
    ForcesRelativeCCC (wetzelTaggedWork site H A) := by
  classical
  apply relativeCCC_tagged (wetzelRawWork site H A) (decodeWork A) .zero rfl
    (fun v => .work v.1.val v.2)
  · rintro ⟨⟨p,h⟩,q⟩
    simp only [decodeWork,dite_eq_left h]
  · exact relativeCCC_analytic_with_cohen hB _ hP

theorem wetzelTaggedBulk_relativeCCC (hB : BoundsCountableOmegaOneNames B) :
    ForcesRelativeCCC (wetzelTaggedBulk (B := B)) :=
  relativeCCC_tagged (valuedCohen B WetzelCoordinate) decodeBulk .zero rfl .bulk (fun _ => rfl)
    (cohen_forcesRelativeCCC hB)

instance wetzelGoodPrefix_nonempty {a : WetzelStageIndex}
    (old : PrefixValidator a (BasedLabel PreparedBA WetzelCertifiedLabel)) :
    Nonempty (GoodPrefix old) := by
  refine ⟨⟨fun _ => none,by simp [present],?_,?_⟩⟩
  · rintro j ⟨v,h⟩
    cases h
  · intro j hj v h
    cases h

theorem nativeWetzelWork_successor_projectedCCC
    (tail : WetzelTailPolicy) {a b : WetzelStageIndex} (ha : (⊥ : WetzelStageIndex)<a)
    (succ : ∀ i : WetzelStageIndex,i<b ↔ i≤a)
    (site : GroundContinuumSuccIndex → ComplexBits (PreStageAlgebra tail (a := a)))
    (H : GroundContinuumSuccIndex → ℕ → ComplexBits (PreStageAlgebra tail (a := a)))
    (A : GroundContinuumSuccIndex → Prop)
    (hVa : TailStageValues tail (a := a) = CertifiedStageLabel.admits (wetzelTaggedWork site H A))
    (hPrev : ProjectedAntichainCCC (prefixMaskRealization tail ha).project)
    (hB : BoundsCountableOmegaOneNames (PreStageAlgebra tail (a := a)))
    (hP : ForcesRelativeCCC (supportedSymbolicQ site H A)) :
    ProjectedAntichainCCC (prefixMaskRealization tail (ha.trans ((succ a).mpr le_rfl))).project := by
  have hMono : Monotone (TailStageValues tail (a := a)) :=
    hVa.symm ▸ CertifiedStageLabel.admits_mono _
  have ht : TailStageValues tail (a := a) ⊤ = ⊤ := by rw [hVa,CertifiedStageLabel.admits_top]
  apply basedPrefix_successor_projectedCCC tail ha hMono ht succ hPrev
  rw [nativeTailValuePoset_eq_certified tail (wetzelTaggedWork site H A) hMono ht hVa]
  exact relativeCCC_certified _ (wetzelTaggedWork_relativeCCC site H A hB hP)

end JSP000930.Negative
