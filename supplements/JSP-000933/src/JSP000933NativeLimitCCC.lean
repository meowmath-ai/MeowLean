import JSP000933MaskProjectedCCC
import JSP000933FiniteSupportAmalgamation

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport RelativeOCA OpenGraphForcing

theorem restrict_self_le {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}
    {a : A} (p : Before R a) : (restrict p.val a).val ≤ p.val := by
  intro i s hs
  have hi : i<a := p.property i ⟨s,hs⟩
  exact ⟨s,(cut_apply_of_lt hi).trans hs,by
    change R.leAt i (cut (cut p.val.trace a) i) s s
    rw [cut_cut_of_le_r75 p.val.trace hi.le]
    exact R.refl ..⟩

theorem compatible_before_of_prefix_and_disjointTail
    {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}
    {z : A} (p q : Before R z) (a : A)
    (hTail : ∀ i, present p.val.trace i → present q.val.trace i → i<a)
    (h : Compatible (restrict p.val a) (restrict q.val a)) :
    Compatible p q := by
  obtain ⟨r,hrp,hrq⟩ := compatible_of_prefix_and_disjointTail_r76 p.val q.val a hTail h
  exact ⟨restrict r z,(restrict_mono_r75 hrp z).trans (restrict_self_le p),
    (restrict_mono_r75 hrq z).trans (restrict_self_le q)⟩

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

theorem stage_covers_finite_below {z : A} (hz : (⊥ : A)<z)
    (hlim : ∀ i<z, ∃ a, i<a ∧ a<z) (r : Finset A) (hr : ∀ i∈r, i<z) :
    ∃ a, (⊥ : A)<a ∧ a<z ∧ ∀ i∈r, i<a := by
  classical
  induction r using Finset.induction_on with
  | empty =>
    obtain ⟨a,ha,ha'⟩ := hlim ⊥ hz
    exact ⟨a,ha,ha',by simp⟩
  | insert x r hx ih =>
    obtain ⟨b,hb,hbz,hbr⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    obtain ⟨a,ha,haz⟩ := hlim (max b x) (max_lt hbz (hr x (Finset.mem_insert_self x r)))
    refine ⟨a,hb.trans (lt_of_le_of_lt (le_max_left _ _) ha),haz,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with h|h
    · exact h.symm ▸ (lt_of_le_of_lt (le_max_right _ _) ha)
    · exact (hbr i h).trans (lt_of_le_of_lt (le_max_left _ _) ha)

theorem basedPrefix_limit_projectedCCC
    (tail : BasedTailPolicy A B T) (hB : BoundsCountableOmegaOneNames B)
    {z : A} (hz : (⊥ : A)<z) (hlim : ∀ i<z, ∃ a, i<a ∧ a<z)
    (hPrev : ∀ (a : A) (ha : (⊥ : A)<a), a<z →
      ProjectedAntichainCCC (prefixMaskRealization tail ha).project) :
    ProjectedAntichainCCC (prefixMaskRealization tail hz).project := by
  classical
  let J := {a : A // (⊥ : A)<a ∧ a<z}
  apply (prefixMaskRealization tail hz).projectedRowCCC_iff.mp
  apply projectedRowCCC_of_finite_support_limit (J := J) (Stage := fun a => BasedBefore tail a.val)
    hB _ _ (fun p => support p.val)
    (fun a p => (prefixMaskRealization tail a.property.1).mask p)
    (fun _ => Compatible)
    (fun a p => restrict p.val a.val)
  · intro r
    by_cases h : ∃ p q : BasedBefore tail z, support p.val ∩ support q.val=r
    · obtain ⟨p,q,hpq⟩ := h
      have hr (i : A) (hi : i∈r) : i<z := by
        rw [←hpq,Finset.mem_inter] at hi
        exact p.property i ((mem_support_r75 p.val i).mp hi.1)
      obtain ⟨a,ha,haz,hBefore⟩ := stage_covers_finite_below hz hlim r hr
      refine ⟨⟨a,ha,haz⟩,?_⟩
      intro u v hUV h
      apply compatible_before_of_prefix_and_disjointTail u v a _ h
      intro i hu hv
      apply hBefore i
      rw [←hUV,Finset.mem_inter]
      exact ⟨(mem_support_r75 u.val i).mpr hu,(mem_support_r75 v.val i).mpr hv⟩
    · obtain ⟨a,ha,haz⟩ := hlim _ hz
      exact ⟨⟨a,ha,haz⟩,fun p q he _ => False.elim (h ⟨p,q,he⟩)⟩
  · intro a p
    change baseMask tail p.val ≤ baseMask tail (restrict p.val a.val).val
    exact (baseMask_restrict tail p.val a.property.1).ge
  · intro a
    exact (prefixMaskRealization tail a.property.1).projectedRowCCC_iff.mpr
      (hPrev a.val a.property.1 a.property.2)

end ForcingTransport
end JSP000933
