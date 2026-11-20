import JSP000933InteriorLimitCCC

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T] [OrderTop T]
variable [DecidableRel ((· ≤ ·) : T → T → Prop)]

theorem countableAntichains_emptyPrefix_r89 {N : A → Type} {R : Rules N} (b : A)
    (hNone : ¬ ∃ a, a < b) : HasCountableAntichains (Before R b) := by
  intro F hF
  have hSmall : F.Subsingleton := by
    intro p hp q hq
    by_contra hn
    apply hF p hp q hq hn
    refine ⟨p,le_rfl,?_⟩
    change ∀ i, coordinateLE R.leAt i p.1.trace q.1.trace
    intro i s hs
    exact False.elim (hNone ⟨i,q.2 i ⟨s,hs⟩⟩)
  exact hSmall.countable

theorem countableAntichains_allPrefixes_r89 (policy : StagePolicy A T)
    (topOK : ∀ a, policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (step : ∀ a, HasCountableAntichains (Before (iterationRules policy) a) →
      HasCountableAntichains (BooleanTwoStep.Condition (StageOf policy a))) :
    ∀ b, HasCountableAntichains (Before (iterationRules policy) b) := by
  classical
  intro b
  refine wellFounded_lt.induction (C := fun b => HasCountableAntichains (Before (iterationRules policy) b)) b ?_
  · intro b ih
    by_cases hNone : ¬ ∃ a, a < b
    · exact countableAntichains_emptyPrefix_r89 b hNone
    · by_cases hLast : ∃ a < b, ∀ i < b, i ≤ a
      · obtain ⟨a,ha,hAll⟩ := hLast
        have hSucc (i : A) : i < b ↔ i ≤ a :=
          ⟨hAll i,fun h => h.trans_lt ha⟩
        exact countableAntichains_successor_r87 policy hSucc (topOK a) (step a (ih a ha))
      · have hNonempty : ∃ a, a < b := not_not.mp hNone
        have hAbove (a : A) (ha : a < b) : ∃ c < b, a < c := by
          by_contra hh
          apply hLast
          exact ⟨a,ha,fun i hi => le_of_not_gt (fun hn => hh ⟨i,hi,hn⟩)⟩
        exact countableAntichains_internalLimit_r88 b hNonempty hAbove ih

theorem countableAntichains_wholeIteration_r89 (policy : StagePolicy A T)
    (bound : ∀ s : Finset A, ∃ a, ∀ i ∈ s, i < a)
    (topOK : ∀ a, policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (step : ∀ a, HasCountableAntichains (Before (iterationRules policy) a) →
      HasCountableAntichains (BooleanTwoStep.Condition (StageOf policy a))) :
    HasCountableAntichains (IterationCondition policy) :=
  countableAntichains_limit_r77 bound (countableAntichains_allPrefixes_r89 policy topOK step)

def OmegaTwoIndex : Type := (Order.succ (ℵ₁ : Cardinal)).ord.ToType

noncomputable instance : LinearOrder OmegaTwoIndex :=
  inferInstanceAs (LinearOrder ((Order.succ (ℵ₁ : Cardinal)).ord.ToType))

instance : WellFoundedLT OmegaTwoIndex :=
  inferInstanceAs (WellFoundedLT ((Order.succ (ℵ₁ : Cardinal)).ord.ToType))

theorem OmegaTwoIndex_finite_bounded_r89 (s : Finset OmegaTwoIndex) :
    ∃ a : OmegaTwoIndex, ∀ i ∈ s, i < a := by
  classical
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  have hReg : (Order.succ (ℵ₁ : Cardinal)).IsRegular :=
    Cardinal.isRegular_succ Cardinal.isRegular_aleph_one.1
  have ho : Order.IsSuccLimit o := Cardinal.isSuccLimit_ord hReg.1
  let e := Ordinal.ToType.mk (o := o)
  have hPos : 0 < o := Cardinal.lt_ord.mpr (by
    simpa only [Ordinal.card_zero] using (Cardinal.aleph0_pos.trans_le hReg.1))
  have hNext (i : OmegaTwoIndex) : ∃ a : OmegaTwoIndex, i < a := by
    have hOld : (e.symm i).1 < o := (e.symm i).2
    have hNew := ho.add_one_lt hOld
    refine ⟨e ⟨_,hNew⟩,?_⟩
    have hlt : e.symm i < (⟨_,hNew⟩ : ↥(Set.Iio o)) := by
      change (e.symm i).1 < (e.symm i).1 + 1
      exact Order.add_one_le_iff.mp le_rfl
    have ht := e.strictMono hlt
    rw [e.apply_symm_apply i] at ht
    exact ht
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨e ⟨0,hPos⟩,fun i hi => False.elim (Finset.notMem_empty i hi)⟩
  | insert i s hi ih =>
    obtain ⟨a,ha⟩ := ih
    obtain ⟨d,hd⟩ := hNext (max i a)
    refine ⟨d,fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (le_max_left ..).trans_lt hd
    · exact (ha j hj).trans ((le_max_right ..).trans_lt hd)

theorem countableAntichains_omegaTwoIteration_r89 (policy : StagePolicy OmegaTwoIndex T)
    (topOK : ∀ a, policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (step : ∀ a, HasCountableAntichains (Before (iterationRules policy) a) →
      HasCountableAntichains (BooleanTwoStep.Condition (StageOf policy a))) :
    HasCountableAntichains (IterationCondition policy) :=
  countableAntichains_wholeIteration_r89 policy OmegaTwoIndex_finite_bounded_r89 topOK step

end FiniteSupport
end JSP000933
