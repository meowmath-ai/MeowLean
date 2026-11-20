import JSP000933BooleanSmallTwoStep

open scoped Flypitch Cardinal
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open OpenGraphForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private noncomputable def ordinalOfIndex (i : OmegaOneIndex) : Ordinal :=
  ((Ordinal.ToType.mk (o := (ℵ₁ : Cardinal).ord)).symm i).1

private theorem ordinalOfIndex_injective_r83 : Function.Injective ordinalOfIndex := by
  intro i j h
  exact (Ordinal.ToType.mk (o := (ℵ₁ : Cardinal).ord)).symm.injective (Subtype.ext h)

noncomputable def omegaOneCheckName (i : OmegaOneIndex) : bSet B :=
  bSet.check (PSet.ordinalMk (ordinalOfIndex i))

theorem omegaOneCheck_eq_bot_r83 {i j : OmegaOneIndex} (h : i ≠ j) :
    ((omegaOneCheckName i : bSet B) =ᴮ omegaOneCheckName j) = ⊥ :=
  bSet.check_bv_eq_bot_of_not_equiv
    (fun he => h (ordinalOfIndex_injective_r83 (PSet.eq_iff_mk_eq.mpr he)))

theorem check_omegaOne_eq_family_r83 :
    (bSet.check (PSet.ordinalMk ((ℵ₁ : Cardinal).ord)) : bSet B) =
      familyName omegaOneCheckName (fun _ => ⊤) := by
  rw [PSet.ordinalMk_eq_def,bSet.check] <;> rfl

noncomputable def finiteIndexLabel (s : Finset OmegaOneIndex) : bSet B :=
  familyName omegaOneCheckName (fun i => if i ∈ s then ⊤ else ⊥)

theorem finiteIndexLabel_member_r83 (s : Finset OmegaOneIndex) (i : OmegaOneIndex) :
    ((omegaOneCheckName i : bSet B) ∈ᴮ finiteIndexLabel s) =
      if i ∈ s then ⊤ else ⊥ :=
  mem_familyName_self_r70 omegaOneCheckName (fun _ _ h => omegaOneCheck_eq_bot_r83 h) _ i

theorem finiteIndexLabel_eq_bot_r83 {s t : Finset OmegaOneIndex} (h : s ≠ t) :
    ((finiteIndexLabel s : bSet B) =ᴮ finiteIndexLabel t) = ⊥ := by
  have hDiff : ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∈ t ∧ i ∉ s) := by
    by_contra hNone
    apply h
    apply Finset.ext
    intro i
    constructor
    · intro hs
      by_contra ht
      exact hNone ⟨i,Or.inl ⟨hs,ht⟩⟩
    · intro ht
      by_contra hs
      exact hNone ⟨i,Or.inr ⟨ht,hs⟩⟩
  obtain ⟨i,hLeft | hRight⟩ := hDiff
  · apply le_bot_iff.mp
    have hh := bSet.subst_congr_mem_right
      (u := (omegaOneCheckName i : bSet B)) (v := finiteIndexLabel s) (w := finiteIndexLabel t)
    simpa only [finiteIndexLabel_member_r83,ite_eq_left hLeft.1,ite_eq_right hLeft.2,inf_top_eq] using hh
  · apply le_bot_iff.mp
    have hh := bSet.subst_congr_mem_right
      (u := (omegaOneCheckName i : bSet B)) (v := finiteIndexLabel t) (w := finiteIndexLabel s)
    rw [show ((finiteIndexLabel t : bSet B) =ᴮ finiteIndexLabel s) =
      (finiteIndexLabel s =ᴮ finiteIndexLabel t) from bSet.bv_eq_symm] at hh
    simpa only [finiteIndexLabel_member_r83,ite_eq_left hRight.1,ite_eq_right hRight.2,inf_top_eq] using hh

abbrev CliqueLabels := (Finset OmegaOneIndex)ᵒᵈ

noncomputable def cliqueGroundLabel (s : CliqueLabels) : bSet B :=
  finiteIndexLabel (OrderDual.ofDual s)

theorem cliqueGroundLabel_eq_bot_r83 {s t : CliqueLabels} (h : s ≠ t) :
    ((cliqueGroundLabel s : bSet B) =ᴮ cliqueGroundLabel t) = ⊥ :=
  finiteIndexLabel_eq_bot_r83 (fun he => h (congrArg OrderDual.toDual he))

end BooleanNames
end JSP000933
