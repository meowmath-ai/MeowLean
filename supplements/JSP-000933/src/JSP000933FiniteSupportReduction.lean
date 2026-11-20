import JSP000933RegularBooleanPullback
import JSP000933FiniteSupportAmalgamation

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}

theorem conditionTrace_injective_r92 :
    Function.Injective (Condition.trace : Condition R → Trace N) := by
  rintro ⟨p,hFp,hVp⟩ ⟨q,hFq,hVq⟩ h
  change p = q at h
  cases h
  rfl

theorem cut_before_trace_r92 {a : A} (p : Before R a) :
    cut p.1.trace a = p.1.trace := by
  funext i
  by_cases hi : i < a
  · exact cut_apply_of_lt hi
  · rw [cut_apply_of_not_lt hi]
    cases ht : p.1.trace i with
    | none => rfl
    | some t => exact False.elim (hi (p.2 i ⟨t,ht⟩))

theorem restrict_fixed_r92 {a : A} (p : Before R a) :
    restrict p.1 a = p :=
  Subtype.ext (conditionTrace_injective_r92 (cut_before_trace_r92 p))

theorem restrict_restrict_r92 (p : Condition R) {a b : A} (h : a ≤ b) :
    restrict (restrict p b).1 a = restrict p a :=
  Subtype.ext (conditionTrace_injective_r92 (restrict_coherent_r75 p h))

def includeBefore {a b : A} (h : a ≤ b) (q : Before R a) : Before R b :=
  ⟨q.1,fun i hi => (q.2 i hi).trans_le h⟩

def prefixReduction {a b : A} (h : a ≤ b) :
    RestrictionMap (Before R b) (Before R a) where
  toFun := fun p => restrict p.1 a
  monotone := fun p q hpq => restrict_mono_r75 (show p.1 ≤ q.1 from hpq) a
  onto := fun q => ⟨includeBefore h q,restrict_fixed_r92 q⟩
  lift := by
    intro p q hpq
    have hComp : Compatible (restrict p.1 a) (restrict q.1 a) := by
      rw [restrict_fixed_r92 q]
      exact ⟨q,hpq,le_rfl⟩
    have hG := compatible_of_prefix_and_disjointTail_r76 p.1 q.1 a
      (fun i _ hi => q.2 i hi) hComp
    obtain ⟨r,hrp,hrq⟩ := hG
    refine ⟨restrict r b,?_,?_⟩
    · have hm := restrict_mono_r75 hrp b
      rwa [restrict_fixed_r92 p] at hm
    · rw [restrict_restrict_r92 r h]
      have hm := restrict_mono_r75 hrq a
      rwa [restrict_fixed_r92 q] at hm

theorem restriction_le_iff_le_inclusion_r92 {a b : A} (h : a ≤ b)
    (p : Before R b) (q : Before R a) :
    (prefixReduction h).toFun p ≤ q ↔ p ≤ includeBefore h q := by
  constructor
  · intro hp
    change ∀ i, coordinateLE R.leAt i (cut p.1.trace a) q.1.trace at hp
    change ∀ i, coordinateLE R.leAt i p.1.trace q.1.trace
    intro i s hs
    have hi : i < a := q.2 i ⟨s,hs⟩
    obtain ⟨t,ht,hle⟩ := hp i s hs
    exact ⟨t,by simpa [cut,hi] using ht,by
      rw [cut_cut_of_le_r75 p.1.trace hi.le] at hle
      exact hle⟩
  · intro hp
    have hp' : p.1 ≤ q.1 := hp
    have hm := restrict_mono_r75 hp' a
    rwa [restrict_fixed_r92 q] at hm

theorem prefixReduction_basic_r92 {a b : A} (h : a ≤ b) (q : Before R a) :
    (prefixReduction h).boolPullback (imageCondition q) = imageCondition (includeBefore h q) := by
  apply Heyting.Regular.coe_injective
  change (prefixReduction h).lowerPullback ((LowerSet.Iic q)ᶜᶜ) =
    ((LowerSet.Iic (includeBefore h q))ᶜᶜ : LowerSet (Before R b))
  rw [RestrictionMap.lowerPullback_compl_r90,RestrictionMap.lowerPullback_compl_r90]
  have he : (prefixReduction h).lowerPullback (LowerSet.Iic q) = LowerSet.Iic (includeBefore h q) := by
    ext p
    exact restriction_le_iff_le_inclusion_r92 h p q
  rw [he]

end FiniteSupport
end JSP000933
