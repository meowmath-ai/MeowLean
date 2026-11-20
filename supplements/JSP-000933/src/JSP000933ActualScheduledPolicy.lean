import JSP000933EntireNativeRelativeCCC
import JSP000933ActualRelativeCliqueStage

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes

abbrev CliqueLabel := OrderDual (Finset OmegaOneIndex)

structure ScheduledGraph (C : Type) [CompleteBooleanAlgebra C] where
  D : (ℕ→C)→C
  K : Word×Word→C
  mark : C

noncomputable def ScheduledGraph.iterandValues {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) : CliqueLabel → C := by
  classical
  exact if h : Nonempty (RelativeCliqueStageData H.D H.K H.mark) then
    (Classical.choice h).iterand.valid else fun _ => ⊤

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem ScheduledGraph.iterandValues_active {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) (h : Nonempty (RelativeCliqueStageData H.D H.K H.mark)) :
    H.iterandValues = (Classical.choice h).iterand.valid := by
  classical
  exact dite_eq_left h

theorem ScheduledGraph.iterandValues_monotone {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) : Monotone H.iterandValues := by
  classical
  by_cases h : Nonempty (RelativeCliqueStageData H.D H.K H.mark)
  · rw [H.iterandValues_active h]
    intro p q hpq
    let S := Classical.choice h
    change cliqueAdmitted H.mark (fun i => H.D (S.points i))
      (fun i j => colorValue H.K (S.points i) (S.points j)) (OrderDual.ofDual p) ≤
      cliqueAdmitted H.mark (fun i => H.D (S.points i))
        (fun i j => colorValue H.K (S.points i) (S.points j)) (OrderDual.ofDual q)
    exact cliqueAdmitted_anti_r121 H.mark _ _ hpq
  · simp [ScheduledGraph.iterandValues,h,Monotone]

theorem ScheduledGraph.iterandValues_top {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) : H.iterandValues ⊤ = ⊤ := by
  classical
  by_cases h : Nonempty (RelativeCliqueStageData H.D H.K H.mark)
  · rw [H.iterandValues_active h]
    exact (Classical.choice h).iterand.weakest_valid
  · simp [ScheduledGraph.iterandValues,h]

noncomputable def ScheduledGraph.quotient {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) : ValuedPoset C CliqueLabel :=
  staticValuedPoset H.iterandValues H.iterandValues_monotone H.iterandValues_top

theorem valuedPoset_eq_of_fields {C N : Type} [CompleteBooleanAlgebra C]
    {P Q : ValuedPoset C N} (hV : P.valid = Q.valid)
    (hR : P.refines = Q.refines) (hW : P.weakest = Q.weakest) : P=Q := by
  cases P
  cases Q
  cases hV
  cases hR
  cases hW
  rfl

theorem ScheduledGraph.quotient_active {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) (h : Nonempty (RelativeCliqueStageData H.D H.K H.mark)) :
    H.quotient = (Classical.choice h).iterand := by
  classical
  apply valuedPoset_eq_of_fields (H.iterandValues_active h)
  · funext p q
    by_cases hp : p≤q
    · have hs : OrderDual.ofDual q ⊆ OrderDual.ofDual p := hp
      simp [ScheduledGraph.quotient,staticValuedPoset,RelativeCliqueStageData.iterand,
        relativeCliquePoset,H.iterandValues_active h,hp,hs]
      intro hn
      exact (hn hs).elim
    · have hs : ¬ (OrderDual.ofDual q ⊆ OrderDual.ofDual p) := hp
      simp [ScheduledGraph.quotient,staticValuedPoset,RelativeCliqueStageData.iterand,
        relativeCliquePoset,H.iterandValues_active h,hp,hs]
      intro hy
      exact (hs hy).elim
  · rfl

theorem ScheduledGraph.quotient_relativeCCC {C : Type} [CompleteBooleanAlgebra C]
    (H : ScheduledGraph C) : ForcesRelativeCCC H.quotient := by
  classical
  by_cases h : Nonempty (RelativeCliqueStageData H.D H.K H.mark)
  · rw [H.quotient_active h]
    exact (Classical.choice h).relativeCCC
  · intro W _ hSep
    have hCommon (p q : CliqueLabel) : commonRefinementValue H.quotient p q = ⊤ := by
      apply top_unique
      let r : CliqueLabel := OrderDual.toDual (OrderDual.ofDual p ∪ OrderDual.ofDual q)
      apply le_iSup_of_le r
      have hp : r ≤ p := Finset.subset_union_left
      have hq : r ≤ q := Finset.subset_union_right
      simp [ScheduledGraph.quotient,staticValuedPoset,ScheduledGraph.iterandValues,h,hp,hq]
    apply le_bot_iff.mp
    apply (unboundedValue_le_pairOverlap_r431 _).trans
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    rw [iSup_inf_iSup]
    apply iSup_le
    rintro ⟨p,q⟩
    exact (by simpa only [hCommon p q,inf_top_eq] using hSep i j.val j.property p q :
      W i p ⊓ W j.val q = ⊥).le

variable {A B : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B]

abbrev ActualScheduleDecoder (A B : Type) [LinearOrder A] [CompleteBooleanAlgebra B] :=
  (a : A) → (old : PrefixValidator a (BasedLabel B CliqueLabel)) →
    ScheduledGraph (RO (GoodPrefix old))

noncomputable def scheduledTail (decode : ActualScheduleDecoder A B) :
    BasedTailPolicy A B CliqueLabel :=
  fun a old => (decode a old).iterandValues

theorem scheduledTail_prefix_projectedCCC (decode : ActualScheduleDecoder A B)
    (hB : BoundsCountableOmegaOneNames B) (a : A) (ha : (⊥ : A)<a) :
    ProjectedAntichainCCC (prefixMaskRealization (scheduledTail decode) ha).project := by
  apply basedPrefix_all_projectedCCC _ hB _ a ha
  intro i _ _
  let H := decode i (earlierValidated (basedPolicy (scheduledTail decode)) i)
  exact ⟨H.iterandValues_monotone,H.iterandValues_top,H.quotient_relativeCCC⟩

theorem scheduledTail_whole_projectedCCC [NoMaxOrder A] (decode : ActualScheduleDecoder A B)
    (hB : BoundsCountableOmegaOneNames B) :
    ProjectedAntichainCCC (basedMaskRealization (scheduledTail decode)).project :=
  basedWhole_projectedCCC _ hB (scheduledTail_prefix_projectedCCC decode hB)

end ForcingTransport
end JSP000933
