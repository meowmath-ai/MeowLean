import Mathlib.Order.Heyting.Regular
import Mathlib.Order.UpperLower.Principal
import Mathlib.Order.CompleteBooleanAlgebra

namespace JSP000933
namespace BooleanCompletion

universe u

abbrev RO (P : Type u) [Preorder P] := Heyting.Regular (LowerSet P)

noncomputable instance completeBooleanAlgebra (P : Type u) [Preorder P] :
    CompleteBooleanAlgebra (RO P) where
  __ := (inferInstance : BooleanAlgebra (RO P))
  __ := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice

variable {P : Type u} [Preorder P]

theorem mem_pseudoCompl_r50 (U : LowerSet P) (p : P) :
    p ∈ (Uᶜ : LowerSet P) ↔ ∀ q ≤ p, q ∉ U := by
  rw [← LowerSet.Iic_le,le_compl_iff_disjoint_left]
  constructor
  · intro h q hq hU
    have hb : U ⊓ LowerSet.Iic p ≤ ⊥ := disjoint_iff_inf_le.mp h
    have hm : q ∈ U ⊓ LowerSet.Iic p := ⟨hU,hq⟩
    have hbot : q ∈ (⊥ : LowerSet P) := hb hm
    simpa using hbot
  · intro h
    apply disjoint_iff_inf_le.mpr
    intro q hq
    exact False.elim (h q hq.2 hq.1)

theorem mem_doublePseudoCompl_r50 (U : LowerSet P) (p : P) :
    p ∈ (Uᶜᶜ : LowerSet P) ↔ ∀ q ≤ p, ∃ r ≤ q, r ∈ U := by
  classical
  rw [mem_pseudoCompl_r50]
  constructor
  · intro h q hq
    by_contra hn
    apply h q hq
    apply (mem_pseudoCompl_r50 U q).mpr
    intro r hr hU
    exact hn ⟨r,hr,hU⟩
  · intro h q hq hneg
    obtain ⟨r,hr,hU⟩ := h q hq
    exact (mem_pseudoCompl_r50 U q).mp hneg r hr hU

def imageCondition (p : P) : RO P := Heyting.Regular.toRegular (LowerSet.Iic p)

theorem imageCondition_mem_r50 (p : P) : p ∈ (imageCondition p : LowerSet P) := by
  change p ∈ ((LowerSet.Iic p)ᶜᶜ : LowerSet P)
  exact (mem_doublePseudoCompl_r50 _ p).mpr (fun q hq => ⟨q,le_rfl,hq⟩)

theorem imageCondition_ne_bot_r50 (p : P) : imageCondition p ≠ ⊥ := by
  intro h
  have hp := imageCondition_mem_r50 p
  rw [h] at hp
  change p ∈ (⊥ : LowerSet P) at hp
  simpa using hp

theorem imageCondition_mono_r50 : Monotone (@imageCondition P _) := by
  intro a b hab
  apply Heyting.Regular.toRegular.monotone
  intro r hr
  exact hr.trans hab

theorem nonbot_exists_member_r50 {U : RO P} (hU : U ≠ ⊥) :
    ∃ p : P, p ∈ (U : LowerSet P) := by
  classical
  by_contra hn
  apply hU
  apply Heyting.Regular.coe_injective
  change (U : LowerSet P) = (⊥ : LowerSet P)
  ext p
  constructor
  · intro h
    exact False.elim (hn ⟨p,h⟩)
  · intro h
    simp at h

theorem imageCondition_dense_r50 (U : RO P) (hU : U ≠ ⊥) :
    ∃ p : P, imageCondition p ≤ U := by
  obtain ⟨p,hp⟩ := nonbot_exists_member_r50 hU
  exact ⟨p,(Heyting.Regular.gi.gc _ _).mpr (LowerSet.Iic_le.mpr hp)⟩

def Compatible (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

theorem compatible_iff_not_disjoint_r50 (p q : P) :
    Compatible p q ↔ ¬ Disjoint (imageCondition p) (imageCondition q) := by
  constructor
  · rintro ⟨r,hrp,hrq⟩ h
    have hp : imageCondition r ≤ imageCondition p := imageCondition_mono_r50 hrp
    have hq : imageCondition r ≤ imageCondition q := imageCondition_mono_r50 hrq
    exact imageCondition_ne_bot_r50 r (le_bot_iff.mp ((le_inf hp hq).trans (disjoint_iff_inf_le.mp h)))
  · intro h
    have hMeet : imageCondition p ⊓ imageCondition q ≠ ⊥ :=
      fun he => h (disjoint_iff_inf_le.mpr he.le)
    obtain ⟨x,hx⟩ := nonbot_exists_member_r50 hMeet
    have hx' : x ∈ ((LowerSet.Iic p)ᶜᶜ : LowerSet P) ∧
        x ∈ ((LowerSet.Iic q)ᶜᶜ : LowerSet P) := hx
    obtain ⟨y,hy,hyp⟩ := (mem_doublePseudoCompl_r50 _ x).mp hx'.1 x le_rfl
    obtain ⟨z,hz,hzq⟩ := (mem_doublePseudoCompl_r50 _ x).mp hx'.2 y hy
    exact ⟨z,hz.trans hyp,hzq⟩

end BooleanCompletion
end JSP000933
