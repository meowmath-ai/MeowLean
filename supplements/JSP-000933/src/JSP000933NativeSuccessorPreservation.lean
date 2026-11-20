import JSP000933NativeMarkedSuccessor
import JSP000933MarkedNameTransport
import JSP000933RelativeOmegaOnePreservation
import JSP000933InteriorNameReflection
import JSP000933PartialHistoryEmbedding

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion BooleanNames MarkedForcing RelativeOCA FiniteSupport

section OrderIso
variable {B C D : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
  [CompleteBooleanAlgebra D]

noncomputable def completeValueMapOfIso (F : B ≃o C) : CompleteValueMap B C where
  toFun := F
  injective := F.injective
  monotone := F.monotone
  map_bot := F.map_bot
  map_top := F.map_top
  map_compl := by
    intro b
    symm
    apply IsCompl.compl_eq
    refine IsCompl.of_eq ?_ ?_
    · rw [← F.map_inf, inf_compl_eq_bot', F.map_bot]
    · rw [← F.map_sup, sup_compl_eq_top, F.map_top]
  map_inf := F.map_inf
  map_iSup := F.map_iSup
  map_iInf := F.map_iInf

noncomputable def composeCompleteValueMaps (F : CompleteValueMap B C)
    (G : CompleteValueMap C D) : CompleteValueMap B D where
  toFun := G.toFun ∘ F.toFun
  injective := G.injective.comp F.injective
  monotone := G.monotone.comp F.monotone
  map_bot := by simp only [Function.comp_apply,F.map_bot,G.map_bot]
  map_top := by simp only [Function.comp_apply,F.map_top,G.map_top]
  map_compl := fun b => by simp only [Function.comp_apply,F.map_compl,G.map_compl]
  map_inf := fun a b => by simp only [Function.comp_apply,F.map_inf,G.map_inf]
  map_iSup := fun f => by simp only [Function.comp_apply,F.map_iSup,G.map_iSup]
  map_iInf := fun f => by simp only [Function.comp_apply,F.map_iInf,G.map_iInf]

theorem rowBounds_ofIso (F : B ≃o C) (h : BoundsCountableOmegaOneNames B) :
    BoundsCountableOmegaOneNames C := by
  intro V
  have hh := F.monotone (h (fun n i => F.symm (V n i)))
  simpa only [OrderIso.map_iInf,OrderIso.map_iSup,F.apply_symm_apply] using hh

end OrderIso

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]
variable (tail : BasedTailPolicy A B T) {a b : A} (ha : a ≠ ⊥)
  (hVa : Monotone (TailStageValues tail (a := a)))
  (hTop : TailStageValues tail (a := a) ⊤ = ⊤)
  (succ : ∀ i : A, i < b ↔ i ≤ a)

noncomputable def markedSuccessorPullIso :
    TotalBA (ExactTailIterand tail hVa hTop) ≃o RO (BasedBefore tail b) :=
  (markedSuccessorComparison tail ha hVa hTop succ).pullIso

include ha succ in
theorem actualMarkedSuccessor_preservesOmegaOne
    (hPrev : BoundsCountableOmegaOneNames (PreStageAlgebra tail (a := a)))
    (hCCC : ForcesRelativeCCC (ExactTailIterand tail hVa hTop)) :
    BoundsCountableOmegaOneNames (RO (BasedBefore tail b)) :=
  rowBounds_ofIso (markedSuccessorPullIso tail ha hVa hTop succ)
    (relativeCCC_preserves_boundsOmegaOne_r436 _ hPrev hCCC)

theorem markedSuccessor_base_commutes (u : PreStageAlgebra tail (a := a)) :
    (markedSuccessorPullIso tail ha hVa hTop succ) (baseEmbed _ u) =
      (prefixReduction (((succ a).mpr le_rfl).le)).boolPullback
        ((orderIsoReduction (prefixOrderIso_r85 (basedPolicy tail) a)).boolPullback u) := by
  let E := markedSuccessorComparison tail ha hVa hTop succ
  change E.pull (baseEmbed _ u) = _
  have test (p : BasedBefore tail b) :
      imageCondition p ≤ E.pull (baseEmbed _ u) ↔
        imageCondition (typedRestrict (basedPolicy tail) p.val a) ≤ u := by
    rw [image_le_iff_member]
    change E.map p ∈ (↑(baseEmbed (ExactTailIterand tail hVa hTop) u) :
      LowerSet (TotalCondition (ExactTailIterand tail hVa hTop))) ↔ _
    rw [← image_le_iff_member]
    exact baseEmbed_reflects_mask_r427 (E.map p) u
  apply le_antisymm
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback,image_le_regular_pullback]
    exact (test p).mp hp
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback,image_le_regular_pullback] at hp
    exact (test p).mpr hp

end ForcingTransport
end JSP000933
