import JSP000933PartialHistoryEmbedding

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion BooleanTwoStep OpenGraphForcing

theorem conditionCCC_of_compatible_reflection_r133 {P Q : Type} [Preorder P] [Preorder Q]
    (f : P → Q) (hReflect : ∀ p q, Compatible (f p) (f q) → Compatible p q)
    (hCCC : HasCountableAntichains Q) : HasCountableAntichains P := by
  classical
  intro S hS
  have hInj : Set.InjOn f S := by
    intro p hp q hq he
    by_contra hn
    exact hS p hp q hq hn (hReflect p q ⟨f p,le_rfl,he.le⟩)
  have hImg : (f '' S).Countable := by
    apply hCCC
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hne hh
    exact hS p hp q hq (fun h => hne (congrArg f h)) (hReflect p q hh)
  exact Set.countable_of_injective_of_countable_image hInj hImg

variable {T B : Type} [Preorder T] [OrderTop T] [DecidableEq T]
variable [DecidableRel ((· ≤ ·) : T → T → Prop)] [CompleteBooleanAlgebra B]

def idleAdmission (s : T) : B := if s = ⊤ then ⊤ else ⊥

theorem idleAdmission_top_r133 : idleAdmission (⊤ : T) = (⊤ : B) := by
  simp [idleAdmission]

theorem idleLabel_eq_top_r133 (q : BooleanTwoStep.Condition (staticLabelStage (idleAdmission : T → B))) :
    q.name = ⊤ := by
  by_contra h
  have hn : q.base ≤ idleAdmission q.name := q.admitted
  rw [idleAdmission,ite_eq_right h] at hn
  exact q.nonzero (le_bot_iff.mp hn)

theorem idleStage_countableAntichains_r133 (hCCC : BooleanCCC B) :
    HasCountableAntichains (BooleanTwoStep.Condition (staticLabelStage (idleAdmission : T → B))) := by
  classical
  intro S hS
  let f (q : BooleanTwoStep.Condition (staticLabelStage (idleAdmission : T → B))) := q.base
  have hComp (p q : BooleanTwoStep.Condition (staticLabelStage (idleAdmission : T → B)))
      (hN : p.base ⊓ q.base ≠ ⊥) : Compatible p q := by
    let w : BooleanTwoStep.Condition (staticLabelStage (idleAdmission : T → B)) :=
      ⟨p.base ⊓ q.base,⊤,hN,(le_top : p.base ⊓ q.base ≤ ⊤).trans_eq idleAdmission_top_r133.symm⟩
    have hp : (⊤ : T) ≤ p.name := (idleLabel_eq_top_r133 p).ge
    have hq : (⊤ : T) ≤ q.name := (idleLabel_eq_top_r133 q).ge
    exact ⟨w,⟨inf_le_left,by simp [w,staticLabelStage,hp]⟩,
      ⟨inf_le_right,by simp [w,staticLabelStage,hq]⟩⟩
  have hInj : Set.InjOn f S := by
    intro p hp q hq h
    by_contra hn
    apply hS p hp q hq hn
    apply hComp
    change p.base = q.base at h
    rw [← h]
    simpa using p.nonzero
  have hCount : (f '' S).Countable := by
    apply hCCC
    · rintro _ ⟨p,hp,rfl⟩
      exact p.nonzero
    · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hDiff
      apply disjoint_iff_inf_le.mpr
      apply le_of_eq
      by_contra hn
      have hNe : p ≠ q := fun h => hDiff (congrArg f h)
      exact hS p hp q hq hNe (hComp p q hn)
  exact Set.countable_of_injective_of_countable_image hInj hCount

end FiniteSupport
end JSP000933
