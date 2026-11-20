import JSP000933ActualComplementarySections

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def NamedContinuousOn (p : B) (f : (ℕ → B) → ℕ → B) : Prop :=
  ∀ (x : ℕ → B) (N : ℕ) (q : B), q≠⊥ → q≤p →
    ∃ (r : B) (u : Word), r≠⊥ ∧ r≤q ∧ r≤cylinderValue x u ∧
      ∀ (y : ℕ → B) (s : B), s≤r → s≤cylinderValue y u → ∀ m<N, s⊓f x m=s⊓f y m

theorem actualSectionPoint_maskBit_r297 {p : B} (P x y : ℕ → B) (b : Bool) (m : ℕ)
    (h : p⊓x m=p⊓y m) :
    p⊓actualSectionPoint P b x m=p⊓actualSectionPoint P b y m :=
  mask_sup_congr_r211 (mask_inf_congr_r126 rfl h) rfl

theorem actualSectionPoint_samePrefix_r297 {p : B} (P x y : ℕ → B) (b : Bool) (u : Word)
    (hx : p≤cylinderValue x u) (hy : p≤cylinderValue y u) :
    ∀ m<u.length, p⊓actualSectionPoint P b x m=p⊓actualSectionPoint P b y m :=
  fun m hm => actualSectionPoint_maskBit_r297 P x y b m (sameCylinder_mask_r261 hx hy m hm)

theorem actualLex_on_regular_section_continuous_r297 (P : ℕ → B) (b : Bool)
    (K : Word × Word → B) (p : B) (hReg : ∀ x, p≤actualLexRegularValue K (actualSectionPoint P b x)) :
    NamedContinuousOn p (fun x => actualLexSelector K (actualSectionPoint P b x)) := by
  intro x N q hq hqp
  let z := actualSectionPoint P b x
  obtain ⟨r,u,hr,hrq,hR,hSame⟩ := actualLexSelector_regular_prefix_r286 K z N hq (hqp.trans (hReg x))
  obtain ⟨v,hv,t,ht,htr,hT⟩ := exists_decided_initialWord_r136 x u.length r hr
  refine ⟨t,v,ht,htr.trans hrq,hT,?_⟩
  intro y s hst hS
  let w := actualSectionPoint P b y
  have hz : s≤cylinderValue z u := hst.trans (htr.trans hR)
  have hV : ∀ m<u.length, s⊓z m=s⊓w m := fun m hm =>
    actualSectionPoint_samePrefix_r297 P x y b v (hst.trans hT) hS m (hv.symm ▸ hm)
  have he := mask_cylinder_bounded_r278 u hV
  have hw : s≤cylinderValue w u := ((le_inf le_rfl hz).trans_eq he).trans inf_le_right
  exact hSame w s (hst.trans htr) hw

theorem NamedContinuousOn.meet_fixed_r297 {p : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) (z : ℕ → B) :
    NamedContinuousOn p (fun x => bitsMeet z (f x)) := by
  intro x N q hq hqp
  obtain ⟨r,u,hr,hrq,hX,hF⟩ := h x N q hq hqp
  exact ⟨r,u,hr,hrq,hX,fun y s hsr hY m hm => mask_inf_congr_r126 rfl (hF y s hsr hY m hm)⟩

theorem NamedContinuousOn.xor_r297 {p : B} {f g : (ℕ → B) → ℕ → B}
    (hf : NamedContinuousOn p f) (hg : NamedContinuousOn p g) :
    NamedContinuousOn p (fun x => bitsSymmDiff (f x) (g x)) := by
  intro x N q hq hqp
  obtain ⟨r,u,hr,hrq,hF,hF'⟩ := hf x N q hq hqp
  obtain ⟨t,v,ht,htr,hG,hG'⟩ := hg x N r hr (hrq.trans hqp)
  rcases le_total u.length v.length with hL | hL
  · have he := extendsWord_of_compatible_r173 x ht hL (htr.trans hF) hG
    refine ⟨t,v,ht,htr.trans hrq,hG,?_⟩
    intro y s hst hY m hm
    exact mask_xor_congr_r257
      (hF' y s (hst.trans htr) (hY.trans (cylinderWord_mono_r173 y he)) m hm)
      (hG' y s hst hY m hm)
  · have he := extendsWord_of_compatible_r173 x ht hL hG (htr.trans hF)
    refine ⟨t,u,ht,htr.trans hrq,htr.trans hF,?_⟩
    intro y s hst hY m hm
    exact mask_xor_congr_r257
      (hF' y s (hst.trans htr) hY m hm)
      (hG' y s hst (hY.trans (cylinderWord_mono_r173 y he)) m hm)

end SetLanguage
end JSP000933
