import JSP000933StaticSuccessor
import JSP000933FiniteSupportLimitCCC

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T] [OrderTop T]
variable [DecidableRel ((· ≤ ·) : T → T → Prop)]

theorem toStaticTwoStep_reflects_compatible_r87 (policy : StagePolicy A T) {a b : A}
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (hTop : policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (p q : Before (iterationRules policy) b)
    (h : Compatible (toStaticTwoStep policy hTop p) (toStaticTwoStep policy hTop q)) :
    Compatible p q := by
  obtain ⟨w,hwp,hwq⟩ := h
  obtain ⟨r,hrp,hrq,hr⟩ := exists_common_prefix_below_r86
    (typedRestrict policy p.1 a) (typedRestrict policy q.1 a) w.nonzero hwp.1 hwq.1
  have hValid : imageCondition r ≤ policy a (earlierValidated policy a) w.name :=
    hr.trans w.admitted
  let c := attachCondition policy succ r w.name hValid
  have aux (z : Before (iterationRules policy) b)
      (hwz : w ≤ toStaticTwoStep policy hTop z) (hrz : r ≤ typedRestrict policy z.1 a) :
      c ≤ z := by
    change ∀ i (s : T), z.1.trace i = some s →
      ∃ t : T, attachTrace r.trace a w.name i = some t ∧ t ≤ s
    intro i s hs
    rcases lt_trichotomy i a with hi | he | hi
    · have hCut : (typedRestrict policy z.1 a).trace i = some s :=
        (cut_apply_of_lt hi).trans hs
      obtain ⟨t,ht,hts⟩ := hrz i s hCut
      exact ⟨t,by simpa [attachTrace,hi.ne] using ht,hts⟩
    · subst i
      have hLeValue : w.base ≤ if w.name ≤ s then ⊤ else ⊥ := by
        have hh := hwz.2
        change w.base ≤ (if w.name ≤ (z.1.trace a).getD ⊤ then ⊤ else ⊥) at hh
        rw [hs] at hh
        exact hh
      have hle : w.name ≤ s := by
        by_contra hn
        rw [ite_eq_right hn] at hLeValue
        exact w.nonzero (le_bot_iff.mp hLeValue)
      exact ⟨w.name,by simp [attachTrace],hle⟩
    · exact False.elim (hi.not_ge ((succ i).mp (z.2 i ⟨s,hs⟩)))
  exact ⟨c,aux p hwp hrp,aux q hwq hrq⟩

theorem countableAntichains_successor_r87 (policy : StagePolicy A T) {a b : A}
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (hTop : policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (hCCC : HasCountableAntichains (BooleanTwoStep.Condition (StageOf policy a))) :
    HasCountableAntichains (Before (iterationRules policy) b) := by
  classical
  intro F hF
  let f := toStaticTwoStep policy hTop (b := b)
  have hI : Set.InjOn f F := by
    intro p hp q hq he
    by_contra hn
    exact hF p hp q hq hn
      (toStaticTwoStep_reflects_compatible_r87 policy succ hTop p q ⟨f p,le_rfl,he.le⟩)
  have hCount : (f '' F).Countable := by
    apply hCCC
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hne hc
    exact hF p hp q hq (fun h => hne (congrArg f h))
      (toStaticTwoStep_reflects_compatible_r87 policy succ hTop p q hc)
  exact Set.countable_of_injective_of_countable_image hI hCount

end FiniteSupport
end JSP000933
