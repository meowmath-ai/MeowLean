import JSP000933CliqueLabelValidity

namespace JSP000933
namespace BooleanCompletion

variable {B C D : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
  [CompleteBooleanAlgebra D]

def CompleteValueMap.comp (G : CompleteValueMap C D) (F : CompleteValueMap B C) :
    CompleteValueMap B D where
  toFun := G.toFun ∘ F.toFun
  injective := G.injective.comp F.injective
  monotone := G.monotone.comp F.monotone
  map_bot := (congrArg G.toFun F.map_bot).trans G.map_bot
  map_top := (congrArg G.toFun F.map_top).trans G.map_top
  map_compl := fun b => (congrArg G.toFun (F.map_compl b)).trans (G.map_compl _)
  map_inf := fun x y => (congrArg G.toFun (F.map_inf x y)).trans (G.map_inf _ _)
  map_iSup := fun f => (congrArg G.toFun (F.map_iSup f)).trans (G.map_iSup _)
  map_iInf := fun f => (congrArg G.toFun (F.map_iInf f)).trans (G.map_iInf _)

def orderIsoReduction {P Q : Type} [Preorder P] [Preorder Q] (e : P ≃o Q) :
    RestrictionMap P Q where
  toFun := e
  monotone := e.monotone
  onto := e.surjective
  lift := by
    intro p q h
    exact ⟨e.symm q,by simpa using e.symm.monotone h,by simp⟩

theorem orderIsoReduction_basic_r122 {P Q : Type} [Preorder P] [Preorder Q]
    (e : P ≃o Q) (q : Q) :
    (orderIsoReduction e).boolPullback (imageCondition q) = imageCondition (e.symm q) := by
  apply Heyting.Regular.coe_injective
  change (orderIsoReduction e).lowerPullback ((LowerSet.Iic q)ᶜᶜ) =
    ((LowerSet.Iic (e.symm q))ᶜᶜ : LowerSet P)
  rw [RestrictionMap.lowerPullback_compl_r90,RestrictionMap.lowerPullback_compl_r90]
  have h : (orderIsoReduction e).lowerPullback (LowerSet.Iic q) = LowerSet.Iic (e.symm q) := by
    ext p
    change e p ≤ q ↔ p ≤ e.symm q
    exact ⟨fun h => by simpa using e.symm.monotone h,fun h => by simpa using e.monotone h⟩
  rw [h]

end BooleanCompletion

namespace FiniteSupport

open BooleanCompletion

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T]

noncomputable def typedStageMap (policy : StagePolicy A T) {a b : A} (hab : a ≤ b) :
    CompleteValueMap (RO (GoodPrefix (earlierValidated policy a)))
      (RO (Before (iterationRules policy) b)) :=
  (prefixReduction hab).completeValueMap.comp
    (orderIsoReduction (prefixOrderIso_r85 policy a)).completeValueMap

theorem typedStageMap_basic_r122 (policy : StagePolicy A T) {a b : A} (hab : a ≤ b)
    (q : GoodPrefix (earlierValidated policy a)) :
    (typedStageMap policy hab).toFun (imageCondition q) =
      imageCondition (includeBefore hab ((prefixOrderIso_r85 policy a).symm q)) := by
  change (prefixReduction hab).boolPullback
    ((orderIsoReduction (prefixOrderIso_r85 policy a)).boolPullback (imageCondition q)) = _
  rw [orderIsoReduction_basic_r122,prefixReduction_basic_r92]

theorem image_le_typedStageMap_restrict_r122 (policy : StagePolicy A T) {a b : A} (hab : a ≤ b)
    (p : Before (iterationRules policy) b) :
    imageCondition p ≤ (typedStageMap policy hab).toFun (imageCondition (typedRestrict policy p.1 a)) := by
  rw [typedStageMap_basic_r122]
  unfold typedRestrict
  rw [OrderIso.symm_apply_apply]
  exact imageCondition_mono_r50 ((restriction_le_iff_le_inclusion_r92 hab p _).mp le_rfl)

end FiniteSupport
end JSP000933
