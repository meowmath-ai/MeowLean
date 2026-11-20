import JSP000933ActualRelativeCliqueCCC
import JSP000933RelativeGenericUnboundedSupport

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing MarkedForcing

variable {B : Type} [CompleteBooleanAlgebra B]

structure RelativeCliqueStageData (D : (ℕ→B)→B) (K : Word×Word→B) (m : B) where
  points : OmegaOneIndex→ℕ→B
  present : ∀ i,m≤D (points i)
  distinct : ∀ i j,i≠j→Disjoint m (realEqValue (points i) (points j))
  relativeCCC : ForcesRelativeCCC
    (relativeCliquePoset m (fun i => D (points i)) (fun i j => colorValue K (points i) (points j)))

noncomputable def RelativeCliqueStageData.iterand
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m) :
    ValuedPoset B (Finset OmegaOneIndex) :=
  relativeCliquePoset m (fun i => D (S.points i)) (fun i j => colorValue K (S.points i) (S.points j))

noncomputable def RelativeCliqueStageData.membership
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m)
    (i : OmegaOneIndex) : TotalBA S.iterand :=
  genericVertexValue m (fun i => D (S.points i)) (fun i j => colorValue K (S.points i) (S.points j)) i

theorem RelativeCliqueStageData.membership_support
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m)
    (i : OmegaOneIndex) : supportProjection S.iterand (S.membership i) = m ⊓ D (S.points i) := by
  unfold RelativeCliqueStageData.iterand RelativeCliqueStageData.membership
  rw [genericVertex_support_r437]

theorem RelativeCliqueStageData.membership_edge
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m)
    {i j : OmegaOneIndex} (hij : i ≠ j) : S.membership i ⊓ S.membership j ≤
      baseEmbed S.iterand (colorValue K (S.points i) (S.points j)) := by
  unfold RelativeCliqueStageData.iterand RelativeCliqueStageData.membership
  exact genericVertex_edge_r437 m (fun a => D (S.points a))
    (fun a b => colorValue K (S.points a) (S.points b)) hij

theorem exists_actualRelativeCliqueStage_r463 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (hD : RealTestExt D) (K : Word×Word→B) (m : B)
    (hNo : ∀ c : CoverCode B,m≤(goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ x,m⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(m⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e) :
    Nonempty (RelativeCliqueStageData D K m) := by
  obtain ⟨Y,hY,hDistinct,hAvoid⟩ :=
    exists_relativeAvoidanceSequence_r442 D hD K m hNo hIrr (relativeScheduleFromEnum e)
  exact ⟨⟨Y,hY,hDistinct,actual_relativeCliqueCCC_r462 hB D K m hIrr hSym Y hY e hE hAvoid⟩⟩

theorem RelativeCliqueStageData.preservesOmegaOne_r463
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m)
    (hB : BoundsCountableOmegaOneNames B) : BoundsCountableOmegaOneNames (TotalBA S.iterand) :=
  relativeCCC_preserves_boundsOmegaOne_r436 S.iterand hB S.relativeCCC

theorem RelativeCliqueStageData.unboundedSupport_r463
    {D : (ℕ→B)→B} {K : Word×Word→B} {m : B} (S : RelativeCliqueStageData D K m) :
    m ≤ supportProjection S.iterand (unboundedValue S.membership) := by
  apply relativeCCC_unbounded_support_r438 S.iterand S.relativeCCC
  intro i
  unfold RelativeCliqueStageData.iterand RelativeCliqueStageData.membership
  rw [genericVertex_support_r437,inf_eq_left.mpr (S.present i)]

end RelativeOCA
end JSP000933
