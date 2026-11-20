import JSP000933CCCMain
import JSP000933BooleanCompletion

namespace JSP000933
namespace OpenGraphForcing

open BooleanCompletion

def CliqueCondition {X : Type} (K : Set (X × X)) (Y : OmegaOneIndex → X) :=
  {a : Finset OmegaOneIndex // FiniteClique (IndexedEdge K Y) a}

instance cliqueCondition_preorder {X : Type} (K : Set (X × X)) (Y : OmegaOneIndex → X) :
    Preorder (CliqueCondition K Y) where
  le a b := b.1 ⊆ a.1
  le_refl := fun _ _ h => h
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

theorem cliqueCondition_compatible_iff_r66 {X : Type} {K : Set (X × X)} {Y : OmegaOneIndex → X}
    (p q : CliqueCondition K Y) :
    Compatible p q ↔ FiniteClique (IndexedEdge K Y) (p.1 ∪ q.1) := by
  constructor
  · rintro ⟨r,hrp,hrq⟩
    exact r.2.subset_r59 (Finset.union_subset hrp hrq)
  · intro h
    exact ⟨⟨p.1 ∪ q.1,h⟩,Finset.subset_union_left,Finset.subset_union_right⟩

def HasCountableAntichains (P : Type*) [Preorder P] : Prop :=
  ∀ F : Set P, (∀ p ∈ F, ∀ q ∈ F, p ≠ q → ¬ Compatible p q) → F.Countable

theorem cliqueCondition_countableAntichains_r66 {X : Type} {K : Set (X × X)} {Y : OmegaOneIndex → X}
    (h : ∀ F : Set (Finset OmegaOneIndex), ¬ F.Countable →
      (∀ a ∈ F, FiniteClique (IndexedEdge K Y) a) →
      ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b)) :
    HasCountableAntichains (CliqueCondition K Y) := by
  classical
  intro F hAnt
  by_contra hFC
  let G := (Subtype.val : CliqueCondition K Y → Finset OmegaOneIndex) '' F
  have hG : ¬ G.Countable := fun h =>
    hFC (Set.countable_of_injective_of_countable_image Subtype.val_injective.injOn h)
  have hCl (a : Finset OmegaOneIndex) (ha : a ∈ G) : FiniteClique (IndexedEdge K Y) a := by
    obtain ⟨p,_,rfl⟩ := ha
    exact p.2
  obtain ⟨a,ha,b,hb,hne,hab⟩ := h G hG hCl
  obtain ⟨p,hp,rfl⟩ := ha
  obtain ⟨q,hq,rfl⟩ := hb
  exact hAnt p hp q hq (fun he => hne (congrArg Subtype.val he))
    ((cliqueCondition_compatible_iff_r66 p q).mpr hab)

def BooleanCCC (B : Type*) [CompleteBooleanAlgebra B] : Prop :=
  ∀ S : Set B, (∀ a ∈ S, a ≠ ⊥) → (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint a b) → S.Countable

theorem booleanCCC_of_conditionCCC_r66 {P : Type*} [Preorder P]
    (hP : HasCountableAntichains P) : BooleanCCC (RO P) := by
  classical
  intro S hNon hDis
  have hEach (b : ↥S) : ∃ p : P, imageCondition p ≤ b.1 :=
    imageCondition_dense_r50 b.1 (hNon b.1 b.2)
  choose p hp using hEach
  have hAnti : ∀ a ∈ Set.range p, ∀ b ∈ Set.range p, a ≠ b → ¬ Compatible a b := by
    rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ hne ⟨w,hwu,hwv⟩
    have hUV : u.1 ≠ v.1 := by
      intro he
      exact hne (congrArg p (Subtype.ext he))
    have hle : imageCondition w ≤ u.1 ⊓ v.1 :=
      le_inf ((imageCondition_mono_r50 hwu).trans (hp u))
        ((imageCondition_mono_r50 hwv).trans (hp v))
    exact imageCondition_ne_bot_r50 w
      (le_bot_iff.mp (hle.trans (disjoint_iff_inf_le.mp (hDis u.1 u.2 v.1 v.2 hUV))))
  have hI : Function.Injective p := by
    intro u v he
    by_contra hn
    have hUV : u.1 ≠ v.1 := fun h => hn (Subtype.ext h)
    have hA : imageCondition (p u) ≤ u.1 ⊓ v.1 := le_inf (hp u) (he.symm ▸ hp v)
    exact imageCondition_ne_bot_r50 (p u)
      (le_bot_iff.mp (hA.trans (disjoint_iff_inf_le.mp (hDis u.1 u.2 v.1 v.2 hUV))))
  have hS : (Set.univ : Set ↥S).Countable :=
    ((hP (Set.range p) hAnti).preimage hI).mono (show (Set.univ : Set ↥S) ⊆ p ⁻¹' Set.range p from fun i _ => Set.mem_range_self i)
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hS)

end OpenGraphForcing
end JSP000933
