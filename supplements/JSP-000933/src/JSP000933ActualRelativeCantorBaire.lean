import JSP000933ActualContinuousTailCodes

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem openValue_sup_code_r303 (K L : Word → B) (x : ℕ → B) :
    openValue (fun u => K u⊔L u) x=openValue K x⊔openValue L x := by
  unfold openValue
  apply le_antisymm
  · apply iSup_le
    intro u
    rw [inf_sup_right]
    exact sup_le_sup (le_iSup (fun w => K w ⊓ cylinderValue x w) u)
      (le_iSup (fun w => L w ⊓ cylinderValue x w) u)
  · apply sup_le
    · exact iSup_le (fun u => le_iSup_of_le u (inf_le_inf_right _ le_sup_left))
    · exact iSup_le (fun u => le_iSup_of_le u (inf_le_inf_right _ le_sup_right))

noncomputable def cylinderOutsideCode (s : Word) : Word → B :=
  boundedTestOpenCode s.length (fun x => (cylinderValue x s)ᶜ)

theorem cylinderOutsideCode_value_r303 (s : Word) (x : ℕ → B) :
    openValue (cylinderOutsideCode s) x=(cylinderValue x s)ᶜ :=
  boundedTestOpenCode_value_r278 s.length _
    ((show BoundedBitLocal s.length (fun x : ℕ → B => cylinderValue x s) from
      fun _ _ _ h => mask_cylinder_bounded_r278 s h).compl_r278) x

def DenseWithinCylinder (p : B) (s : Word) (K : Word → B) : Prop :=
  ∀ u : Word, ExtendsWord s u → p≤⨆ x : ℕ → B, cylinderValue x u⊓openValue K x

theorem incompatibleWords_disjoint_cylinders_r303 (x : ℕ → B) (s u : Word)
    (he : ¬ExtendsWord s u) (hf : ¬ExtendsWord u s) :
    cylinderValue x s⊓cylinderValue x u≤⊥ := by
  let q := cylinderValue x s⊓cylinderValue x u
  by_contra h
  have hq : q≠⊥ := fun he => h he.le
  rcases le_total s.length u.length with hL | hL
  · exact he (extendsWord_of_compatible_r173 x hq hL inf_le_left inf_le_right)
  · exact hf (extendsWord_of_compatible_r173 x hq hL inf_le_right inf_le_left)

theorem DenseWithinCylinder.to_global_r303 {p : B} {s : Word} {K : Word → B}
    (h : DenseWithinCylinder p s K) : DenseOpenNaming p (fun u => K u⊔cylinderOutsideCode s u) := by
  intro u
  by_cases hSU : ExtendsWord s u
  · apply (h u hSU).trans
    exact iSup_le (fun x => le_iSup_of_le x (inf_le_inf_left _
      (openValue_monoCode_r280 (fun _ => le_sup_left) x)))
  by_cases hUS : ExtendsWord u s
  · apply (h s (extendsWord_refl_r216 s)).trans
    exact iSup_le (fun x => le_iSup_of_le x
      (inf_le_inf (cylinderWord_mono_r173 x hUS) (openValue_monoCode_r280 (fun _ => le_sup_left) x)))
  let x := paddedWordBits (B := B) u
  have hu : p≤cylinderValue x u := le_top.trans (paddedWord_in_ownCylinder_r280 u)
  have hs : p≤(cylinderValue x s)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    exact (le_inf (inf_le_left.trans hu) inf_le_right).trans (incompatibleWords_disjoint_cylinders_r303 x u s hUS hSU)
  apply le_iSup_of_le x
  refine le_inf hu ?_
  rw [openValue_sup_code_r303,cylinderOutsideCode_value_r303]
  exact hs.trans le_sup_right

theorem exists_name_meeting_relative_dense_r303 (p : B) (s : Word) (K : ℕ → Word → B)
    (h : ∀ n, DenseWithinCylinder p s (K n)) :
    ∃ x : ℕ → B, p≤cylinderValue x s ∧ ∀ n, p≤openValue (K n) x := by
  obtain ⟨x,hS,hK⟩ := exists_namedReal_meeting_denseOpen_r219 p s
    (fun n u => K n u⊔cylinderOutsideCode s u) (fun n => (h n).to_global_r303)
  refine ⟨x,hS,fun n => ?_⟩
  have hO := hK n
  rw [openValue_sup_code_r303,cylinderOutsideCode_value_r303] at hO
  let C := cylinderValue x s
  change p≤openValue (K n) x⊔Cᶜ at hO
  calc
    p=p⊓(openValue (K n) x⊔Cᶜ) := le_antisymm (le_inf le_rfl hO) inf_le_left
    _=(p⊓openValue (K n) x)⊔(p⊓Cᶜ) := inf_sup_left _ _ _
    _≤openValue (K n) x := sup_le inf_le_right
      (((le_inf (inf_le_left.trans hS) inf_le_right).trans_eq inf_compl_eq_bot').trans bot_le)

end SetLanguage
end JSP000933
