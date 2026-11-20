import JSP000933FiniteSupportAmalgamation
import JSP000933CliqueForcing

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

variable {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}

private theorem pair_with_compatible_images_r77 {U P : Type} [Preorder P]
    (hP : HasCountableAntichains P) (F : Set U) (hF : ¬ F.Countable) (f : U → P) :
    ∃ p ∈ F, ∃ q ∈ F, p ≠ q ∧ Compatible (f p) (f q) := by
  classical
  by_contra h
  have hInj : Set.InjOn f F := by
    intro p hp q hq hpq
    by_contra hn
    exact h ⟨p,hp,q,hq,hn,f p,le_rfl,hpq.le⟩
  have hImage : (f '' F).Countable := by
    apply hP
    rintro a ⟨p,hp,rfl⟩ b ⟨q,hq,rfl⟩ hne hh
    exact h ⟨p,hp,q,hq,fun he => hne (congrArg f he),hh⟩
  exact hF (Set.countable_of_injective_of_countable_image hInj hImage)

private theorem exists_boundedOverlap_r77
    (bound : ∀ s : Finset A, ∃ a, ∀ i ∈ s, i < a)
    (F : Set (Condition R)) (hF : ¬ F.Countable) :
    ∃ E : Set (Condition R), E ⊆ F ∧ ¬ E.Countable ∧
      ∃ a, ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
        ∀ i, present p.trace i → present q.trace i → i < a := by
  classical
  let S := support '' F
  by_cases hS : S.Countable
  · let Fiber (s : Finset A) : Set (Condition R) := {p | p ∈ F ∧ support p = s}
    have hExists : ∃ s ∈ S, ¬ (Fiber s).Countable := by
      by_contra h
      have hEach (s : ↥S) : (Fiber s.1).Countable := by
        by_contra hn
        exact h ⟨s.1,s.2,hn⟩
      letI : Countable (↥S) := hS.to_subtype
      apply hF
      apply (Set.countable_iUnion hEach).mono
      intro p hp
      exact Set.mem_iUnion.mpr ⟨⟨support p,⟨p,hp,rfl⟩⟩,hp,rfl⟩
    obtain ⟨s,hs,hE⟩ := hExists
    obtain ⟨a,ha⟩ := bound s
    refine ⟨Fiber s,fun p hp => hp.1,hE,a,fun p hp _ _ _ i hi _ => ?_⟩
    apply ha i
    rw [← hp.2]
    exact (mem_support_r75 p i).mpr hi
  · obtain ⟨root,G,hG,hGc,hD⟩ := exists_deltaSystem_r74 S hS
    have hSelect (s : ↥G) : ∃ p ∈ F, support p = s.1 := hG s.2
    choose f hfF hfS using hSelect
    have hf : Function.Injective f := by
      intro s t he
      exact Subtype.ext ((hfS s).symm.trans ((congrArg support he).trans (hfS t)))
    obtain ⟨a,ha⟩ := bound root
    refine ⟨Set.range f,?_,?_,a,?_⟩
    · rintro _ ⟨s,rfl⟩
      exact hfF s
    · intro h
      have hh : (Set.univ : Set ↥G).Countable :=
        (h.preimage hf).mono (show (Set.univ : Set ↥G) ⊆ f ⁻¹' Set.range f from fun i _ => Set.mem_range_self i)
      exact hGc (Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hh))
    · rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩ hne i hs ht
      have hst : s.1 ≠ t.1 := fun he => hne (congrArg f (Subtype.ext he))
      apply ha i
      rw [← hD s.1 s.2 t.1 t.2 hst,← hfS s,← hfS t]
      exact Finset.mem_inter.mpr ⟨(mem_support_r75 (f s) i).mpr hs,
        (mem_support_r75 (f t) i).mpr ht⟩

theorem countableAntichains_limit_r77
    (bound : ∀ s : Finset A, ∃ a, ∀ i ∈ s, i < a)
    (prefixCCC : ∀ a : A, HasCountableAntichains (Before R a)) :
    HasCountableAntichains (Condition R) := by
  classical
  intro F hAnti
  by_contra hF
  obtain ⟨E,hEF,hE,a,ha⟩ := exists_boundedOverlap_r77 bound F hF
  obtain ⟨p,hp,q,hq,hne,hComp⟩ :=
    pair_with_compatible_images_r77 (prefixCCC a) E hE (fun p => restrict p a)
  exact hAnti p (hEF hp) q (hEF hq) hne
    (compatible_of_prefix_and_disjointTail_r76 p q a (ha p hp q hq hne) hComp)

end FiniteSupport
end JSP000933
