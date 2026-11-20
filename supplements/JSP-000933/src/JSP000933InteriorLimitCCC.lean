import JSP000933SuccessorCCC

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

variable {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}

private theorem finite_boundedBelowLimit_r88 {b : A}
    (nonempty : ∃ a, a < b) (above : ∀ a < b, ∃ c < b, a < c) :
    ∀ s : Finset A, (∀ i ∈ s, i < b) → ∃ a < b, ∀ i ∈ s, i < a := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨a,ha⟩ := nonempty
    exact ⟨a,ha,fun i hi => False.elim (Finset.notMem_empty i hi)⟩
  | insert i s hi ih =>
    intro h
    have hI : i < b := h i (Finset.mem_insert_self ..)
    obtain ⟨a,ha,hs⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨d,hd,hm⟩ := above (max i a) (max_lt_iff.mpr ⟨hI,ha⟩)
    refine ⟨d,hd,fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (le_max_left ..).trans_lt hm
    · exact (hs j hj).trans ((le_max_right ..).trans_lt hm)

private theorem prefixCompatible_of_global_r88 {b : A} (p q : Before R b)
    (h : Compatible p.1 q.1) : Compatible p q := by
  obtain ⟨r,hrp,hrq⟩ := h
  have aux (x : Before R b) (hx : r ≤ x.1) : restrict r b ≤ x := by
    have hrel := restrict_mono_r75 hx b
    change ∀ i, coordinateLE R.leAt i (cut r.trace b) (cut x.1.trace b) at hrel
    change ∀ i, coordinateLE R.leAt i (cut r.trace b) x.1.trace
    have hCut : cut x.1.trace b = x.1.trace := by
      funext i
      by_cases hi : i < b
      · exact cut_apply_of_lt hi
      · rw [cut_apply_of_not_lt hi]
        cases ht : x.1.trace i with
        | none => rfl
        | some t => exact False.elim (hi (x.2 i ⟨t,ht⟩))
    exact hCut ▸ hrel
  exact ⟨restrict r b,aux p hrp,aux q hrq⟩

private theorem compatibleImages_of_uncountable_r88 {C P : Type} [Preorder P]
    (hP : HasCountableAntichains P) (F : Set C) (hF : ¬ F.Countable) (f : C → P) :
    ∃ p ∈ F, ∃ q ∈ F, p ≠ q ∧ Compatible (f p) (f q) := by
  classical
  by_contra h
  have hInj : Set.InjOn f F := by
    intro p hp q hq he
    by_contra hn
    exact h ⟨p,hp,q,hq,hn,f p,le_rfl,he.le⟩
  have hImage : (f '' F).Countable := by
    apply hP
    rintro a ⟨p,hp,rfl⟩ b ⟨q,hq,rfl⟩ hne hh
    exact h ⟨p,hp,q,hq,fun he => hne (congrArg f he),hh⟩
  exact hF (Set.countable_of_injective_of_countable_image hInj hImage)

private theorem thin_boundedOverlap_r88 {b : A}
    (nonempty : ∃ a, a < b) (above : ∀ a < b, ∃ c < b, a < c)
    (F : Set (Before R b)) (hF : ¬ F.Countable) :
    ∃ E : Set (Before R b), E ⊆ F ∧ ¬ E.Countable ∧
      ∃ a < b, ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
        ∀ i, present p.1.trace i → present q.1.trace i → i < a := by
  classical
  let supOf (p : Before R b) := support p.1
  let S := supOf '' F
  have hBound (s : Finset A) (hs : s ∈ S) : ∀ i ∈ s, i < b := by
    obtain ⟨p,_,rfl⟩ := hs
    exact fun i hi => p.2 i ((mem_support_r75 p.1 i).mp hi)
  by_cases hS : S.Countable
  · let Fiber (s : Finset A) : Set (Before R b) := {p | p ∈ F ∧ supOf p = s}
    have hExists : ∃ s ∈ S, ¬ (Fiber s).Countable := by
      by_contra h
      have hEach (s : ↥S) : (Fiber s.1).Countable := by
        by_contra hn
        exact h ⟨s.1,s.2,hn⟩
      letI : Countable (↥S) := hS.to_subtype
      apply hF
      apply (Set.countable_iUnion hEach).mono
      intro p hp
      exact Set.mem_iUnion.mpr ⟨⟨supOf p,⟨p,hp,rfl⟩⟩,hp,rfl⟩
    obtain ⟨s,hs,hE⟩ := hExists
    obtain ⟨a,ha,hcap⟩ := finite_boundedBelowLimit_r88 nonempty above s (hBound s hs)
    refine ⟨Fiber s,fun p hp => hp.1,hE,a,ha,fun p hp _ _ _ i hi _ => ?_⟩
    apply hcap i
    rw [← hp.2]
    exact (mem_support_r75 p.1 i).mpr hi
  · obtain ⟨root,G,hG,hGc,hD⟩ := exists_deltaSystem_r74 S hS
    have hSelect (s : ↥G) : ∃ p ∈ F, supOf p = s.1 := hG s.2
    choose f hfF hfS using hSelect
    have hf : Function.Injective f := by
      intro s t he
      exact Subtype.ext ((hfS s).symm.trans ((congrArg supOf he).trans (hfS t)))
    have hDistinct : ∃ s ∈ G, ∃ t ∈ G, s ≠ t := by
      by_contra hc
      apply hGc
      have hs : G.Subsingleton := by
        intro s hs t ht
        by_contra hne
        exact hc ⟨s,hs,t,ht,hne⟩
      exact hs.countable
    obtain ⟨s,hs,t,ht,hst⟩ := hDistinct
    have hRoot (i : A) (hi : i ∈ root) : i < b := by
      rw [← hD s hs t ht hst] at hi
      exact hBound s (hG hs) i (Finset.mem_inter.mp hi).1
    obtain ⟨a,ha,hcap⟩ := finite_boundedBelowLimit_r88 nonempty above root hRoot
    refine ⟨Set.range f,?_,?_,a,ha,?_⟩
    · rintro _ ⟨s,rfl⟩
      exact hfF s
    · intro h
      have hh : (Set.univ : Set ↥G).Countable :=
        (h.preimage hf).mono (show (Set.univ : Set ↥G) ⊆ f ⁻¹' Set.range f from fun i _ => Set.mem_range_self i)
      exact hGc (Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hh))
    · rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩ hne i hs ht
      have hst : s.1 ≠ t.1 := fun he => hne (congrArg f (Subtype.ext he))
      apply hcap i
      rw [← hD s.1 s.2 t.1 t.2 hst,← hfS s,← hfS t]
      exact Finset.mem_inter.mpr ⟨(mem_support_r75 (f s).1 i).mpr hs,
        (mem_support_r75 (f t).1 i).mpr ht⟩

theorem countableAntichains_internalLimit_r88 (b : A)
    (nonempty : ∃ a, a < b) (above : ∀ a < b, ∃ c < b, a < c)
    (prefixCCC : ∀ a < b, HasCountableAntichains (Before R a)) :
    HasCountableAntichains (Before R b) := by
  classical
  intro F hAnti
  by_contra hF
  obtain ⟨E,hEF,hE,a,ha,hCap⟩ := thin_boundedOverlap_r88 nonempty above F hF
  obtain ⟨p,hp,q,hq,hne,hComp⟩ :=
    compatibleImages_of_uncountable_r88 (prefixCCC a ha) E hE (fun p => restrict p.1 a)
  apply hAnti p (hEF hp) q (hEF hq) hne
  apply prefixCompatible_of_global_r88 p q
  exact compatible_of_prefix_and_disjointTail_r76 p.1 q.1 a (hCap p hp q hq hne) hComp

end FiniteSupport
end JSP000933
