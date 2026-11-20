import JSP000933ActualFaceRefinementLaws

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem faceRefinement_refl_r328 (p : B) (a z : ℕ → B) : p≤faceRefinementValue a z a z := by
  unfold faceRefinementValue
  apply le_inf (bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl))
  apply le_iInf
  exact fun _ => (le_bitEq_iff_r126 _ _ _).mpr rfl

theorem faceRefinement_of_le_r328 {p : B} (a z : ℕ → ℕ → B)
    (h : ∀ n, p≤faceRefinementValue (a n) (z n) (a (n+1)) (z (n+1))) :
    ∀ i j, i≤j → p≤faceRefinementValue (a i) (z i) (a j) (z j) := by
  intro i j
  induction j with
  | zero =>
    intro hI
    have he : i=0 := Nat.eq_zero_of_le_zero hI
    subst i
    exact faceRefinement_refl_r328 p _ _
  | succ j ih =>
    intro hI
    by_cases he : i=j+1
    · subst i
      exact faceRefinement_refl_r328 p _ _
    · have hIJ : i≤j := by omega
      exact faceRefinement_trans_r327 (ih hIJ) (h j)

noncomputable def actualFaceLimit (a z : ℕ → ℕ → B) (m : ℕ) : B :=
  ⨆ j : ℕ, (a j m)ᶜ⊓z j m

theorem actualFaceLimit_in_all_r328 {p : B} (a z : ℕ → ℕ → B)
    (h : ∀ n, p≤faceRefinementValue (a n) (z n) (a (n+1)) (z (n+1))) :
    ∀ i, p≤faceMembershipValue (a i) (z i) (actualFaceLimit a z) := by
  intro i
  apply (faceMembership_iff_fixed_mask_r327 (a i) (z i) (actualFaceLimit a z)).mpr
  intro m
  let q := p⊓(a i m)ᶜ
  change q⊓actualFaceLimit a z m=q⊓z i m
  apply le_antisymm
  · unfold actualFaceLimit
    rw [inf_iSup_eq]
    apply iSup_le
    intro j
    rcases le_total i j with hIJ | hJI
    · have hF := faceRefinement_of_le_r328 a z h i j hIJ
      have hq : q≤(a j m)ᶜ := (outside_mask_antitone_r327 (hF.trans inf_le_left) m).trans inf_le_right
      calc
        q⊓((a j m)ᶜ⊓z j m)=q⊓z j m := by rw [← inf_assoc,inf_eq_left.mpr hq]
        _=q⊓z i m := (faceRefinement_fixedMask_r327 hF m).symm
        _≤q⊓z i m := le_rfl
    · have hF := faceRefinement_of_le_r328 a z h j i hJI
      let r := q⊓(a j m)ᶜ
      have hr : r≤p⊓(a j m)ᶜ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      calc
        q⊓((a j m)ᶜ⊓z j m)=r⊓z j m := (inf_assoc _ _ _).symm
        _=r⊓z i m := mask_under_r302 hr (faceRefinement_fixedMask_r327 hF m)
        _≤q⊓z i m := inf_le_inf_right _ inf_le_left
  · exact le_inf inf_le_left (le_iSup_of_le i (le_inf (inf_le_left.trans inf_le_right) inf_le_right))

end SetLanguage
end JSP000933
