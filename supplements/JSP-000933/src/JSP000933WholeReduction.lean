import JSP000933CompleteValueMap

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}

def wholeReduction (a : A) : RestrictionMap (Condition R) (Before R a) where
  toFun := fun p => restrict p a
  monotone := fun p q hpq => restrict_mono_r75 hpq a
  onto := fun q => ⟨q.1,restrict_fixed_r92 q⟩
  lift := by
    intro p q hpq
    have hComp : Compatible (restrict p a) (restrict q.1 a) := by
      rw [restrict_fixed_r92 q]
      exact ⟨q,hpq,le_rfl⟩
    have hG := compatible_of_prefix_and_disjointTail_r76 p q.1 a (fun i _ hi => q.2 i hi) hComp
    obtain ⟨r,hrp,hrq⟩ := hG
    refine ⟨r,hrp,?_⟩
    have h := restrict_mono_r75 hrq a
    rwa [restrict_fixed_r92 q] at h

theorem whole_restriction_le_iff_r100 (a : A) (p : Condition R) (q : Before R a) :
    (wholeReduction a).toFun p ≤ q ↔ p ≤ q.1 := by
  constructor
  · intro hp
    change ∀ i, coordinateLE R.leAt i (cut p.trace a) q.1.trace at hp
    change ∀ i, coordinateLE R.leAt i p.trace q.1.trace
    intro i s hs
    have hi : i < a := q.2 i ⟨s,hs⟩
    obtain ⟨t,ht,hle⟩ := hp i s hs
    exact ⟨t,by simpa [cut,hi] using ht,by
      rw [cut_cut_of_le_r75 p.trace hi.le] at hle
      exact hle⟩
  · intro hp
    have hm := restrict_mono_r75 hp a
    rwa [restrict_fixed_r92 q] at hm

theorem wholeReduction_basic_r100 (a : A) (q : Before R a) :
    (wholeReduction a).boolPullback (imageCondition q) = imageCondition q.1 := by
  apply Heyting.Regular.coe_injective
  change (wholeReduction a).lowerPullback ((LowerSet.Iic q)ᶜᶜ) =
    ((LowerSet.Iic q.1)ᶜᶜ : LowerSet (Condition R))
  rw [RestrictionMap.lowerPullback_compl_r90,RestrictionMap.lowerPullback_compl_r90]
  have he : (wholeReduction a).lowerPullback (LowerSet.Iic q) = LowerSet.Iic q.1 := by
    ext p
    exact whole_restriction_le_iff_r100 a p q
  rw [he]

end FiniteSupport
end JSP000933
