import JSP000933FiniteSupportReduction

namespace JSP000933
namespace BooleanCompletion

universe u

structure CompleteValueMap (B C : Type u) [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C] where
  toFun : B → C
  injective : Function.Injective toFun
  monotone : Monotone toFun
  map_bot : toFun ⊥ = ⊥
  map_top : toFun ⊤ = ⊤
  map_compl : ∀ x, toFun xᶜ = (toFun x)ᶜ
  map_inf : ∀ x y, toFun (x ⊓ y) = toFun x ⊓ toFun y
  map_iSup : ∀ {I : Type u} (U : I → B), toFun (⨆ i, U i) = ⨆ i, toFun (U i)
  map_iInf : ∀ {I : Type u} (U : I → B), toFun (⨅ i, U i) = ⨅ i, toFun (U i)

variable {B C : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem CompleteValueMap.map_sup_r93 (F : CompleteValueMap B C) (x y : B) :
    F.toFun (x ⊔ y) = F.toFun x ⊔ F.toFun y := by
  have h : x ⊔ y = (xᶜ ⊓ yᶜ)ᶜ := by simp only [compl_inf,compl_compl]
  rw [h,F.map_compl,F.map_inf,F.map_compl,F.map_compl,compl_inf,compl_compl,compl_compl]

theorem CompleteValueMap.reflect_le_r93 (F : CompleteValueMap B C) {x y : B}
    (h : F.toFun x ≤ F.toFun y) : x ≤ y := by
  have hi : F.toFun (x ⊓ y) = F.toFun x :=
    (F.map_inf x y).trans (inf_eq_left.mpr h)
  exact inf_eq_left.mp (F.injective hi)

noncomputable def RestrictionMap.completeValueMap {P Q : Type u} [Preorder P] [Preorder Q]
    (F : RestrictionMap P Q) : CompleteValueMap (RO Q) (RO P) where
  toFun := F.boolPullback
  injective := F.boolPullback_injective_r91
  monotone := fun U V h => (F.boolPullback_le_iff_r90 U V).mpr h
  map_bot := F.boolPullback_bot_r91
  map_top := F.boolPullback_top_r91
  map_compl := F.boolPullback_compl_r90
  map_inf := F.boolPullback_inf_r91
  map_iSup := F.boolPullback_iSup_r91
  map_iInf := F.boolPullback_iInf_r91

end BooleanCompletion
end JSP000933
