import JSP000933BooleanCompletion

namespace JSP000933
namespace BooleanCompletion

universe u v w
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

structure RestrictionMap (P : Type u) (Q : Type v) [Preorder P] [Preorder Q] where
  toFun : P → Q
  monotone : Monotone toFun
  onto : Function.Surjective toFun
  lift : ∀ p q, q ≤ toFun p → ∃ r ≤ p, toFun r ≤ q

def RestrictionMap.lowerPullback (F : RestrictionMap P Q) (U : LowerSet Q) : LowerSet P :=
  ⟨{p | F.toFun p ∈ U},fun _ _ h hp => U.lower (F.monotone h) hp⟩

theorem RestrictionMap.lowerPullback_compl_r90 (F : RestrictionMap P Q) (U : LowerSet Q) :
    F.lowerPullback Uᶜ = (F.lowerPullback U)ᶜ := by
  ext p
  change F.toFun p ∈ (Uᶜ : LowerSet Q) ↔ p ∈ ((F.lowerPullback U)ᶜ : LowerSet P)
  rw [mem_pseudoCompl_r50,mem_pseudoCompl_r50]
  constructor
  · intro h r hr
    exact h (F.toFun r) (F.monotone hr)
  · intro h q hq hU
    obtain ⟨r,hr,hrq⟩ := F.lift p q hq
    exact h r hr (U.lower hrq hU)

def RestrictionMap.boolPullback (F : RestrictionMap P Q) (U : RO Q) : RO P :=
  ⟨F.lowerPullback (U : LowerSet Q),by
    change (F.lowerPullback (U : LowerSet Q))ᶜᶜ = F.lowerPullback (U : LowerSet Q)
    rw [← F.lowerPullback_compl_r90,← F.lowerPullback_compl_r90,U.prop.eq]⟩

theorem RestrictionMap.boolPullback_le_iff_r90 (F : RestrictionMap P Q) (U V : RO Q) :
    F.boolPullback U ≤ F.boolPullback V ↔ U ≤ V := by
  constructor
  · intro h q hq
    obtain ⟨p,rfl⟩ := F.onto q
    exact h (show p ∈ F.lowerPullback (U : LowerSet Q) from hq)
  · intro h p hp
    exact h (show F.toFun p ∈ (U : LowerSet Q) from hp)

theorem RestrictionMap.boolPullback_compl_r90 (F : RestrictionMap P Q) (U : RO Q) :
    F.boolPullback Uᶜ = (F.boolPullback U)ᶜ := by
  apply Heyting.Regular.coe_injective
  change F.lowerPullback (↑(Uᶜ) : LowerSet Q) = (F.lowerPullback (U : LowerSet Q))ᶜ
  simpa only [Heyting.Regular.coe_compl] using F.lowerPullback_compl_r90 (U : LowerSet Q)

theorem RestrictionMap.lowerPullback_iSup_r90 (F : RestrictionMap P Q) {I : Type w}
    (U : I → LowerSet Q) : F.lowerPullback (⨆ i, U i) = ⨆ i, F.lowerPullback (U i) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi⟩ := LowerSet.mem_iSup_iff.mp
      (show F.toFun p ∈ (⨆ i, U i) from hp)
    exact LowerSet.mem_iSup_iff.mpr ⟨i,hi⟩
  · intro hp
    obtain ⟨i,hi⟩ := LowerSet.mem_iSup_iff.mp hp
    exact LowerSet.mem_iSup_iff.mpr
      (show ∃ i, F.toFun p ∈ U i from ⟨i,hi⟩)

end BooleanCompletion
end JSP000933
