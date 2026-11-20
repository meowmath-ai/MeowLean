import JSP000933ActualBadChildMixing

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem outside_mask_antitone_r327 {p : B} {a b : ℕ → B}
    (h : p≤bitsBelowValue b a) (m : ℕ) : p⊓(a m)ᶜ≤p⊓(b m)ᶜ := by
  apply le_inf inf_le_left
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  exact ((le_inf ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
    (bitsBelowValue_apply_r256 h m)) (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot')

theorem faceMembership_iff_fixed_mask_r327 {p : B} (a z x : ℕ → B) :
    p≤faceMembershipValue a z x ↔
      ∀ m, (p⊓(a m)ᶜ)⊓x m=(p⊓(a m)ᶜ)⊓z m := by
  unfold faceMembershipValue
  constructor
  · intro h m
    let q := p⊓(a m)ᶜ
    have hEq : q⊓namedFacePoint a z x m=q⊓x m :=
      (le_realEqValue_iff_r126 _ _ _).mp (inf_le_left.trans h) m
    calc
      q⊓x m=q⊓namedFacePoint a z x m := hEq.symm
      _=p⊓((a m)ᶜ⊓namedFacePoint a z x m) := inf_assoc _ _ _
      _=p⊓((a m)ᶜ⊓z m) := congrArg (fun b : B => p⊓b) (namedFacePoint_bit_of_fixed_r305 a z x m)
      _=q⊓z m := (inf_assoc _ _ _).symm
  · intro h
    apply (le_realEqValue_iff_r126 _ _ _).mpr
    intro m
    unfold namedFacePoint
    rw [inf_sup_left,← inf_assoc p (a m) (x m),← inf_assoc p (a m)ᶜ (z m),← h m]
    rw [inf_assoc p (a m) (x m),inf_assoc p (a m)ᶜ (x m),← inf_sup_left,← inf_sup_right,
      sup_compl_eq_top,top_inf_eq]

theorem faceRefinement_fixedMask_r327 {p : B} {a z b w : ℕ → B}
    (h : p≤faceRefinementValue a z b w) (m : ℕ) :
    (p⊓(a m)ᶜ)⊓z m=(p⊓(a m)ᶜ)⊓w m := by
  have he := (le_bitEq_iff_r126 _ _ _).mp (h.trans (inf_le_right.trans (iInf_le _ m)))
  simpa only [inf_assoc] using he

theorem faceRefinement_trans_r327 {p : B} {a z b w c v : ℕ → B}
    (h₁ : p≤faceRefinementValue a z b w) (h₂ : p≤faceRefinementValue b w c v) :
    p≤faceRefinementValue a z c v := by
  unfold faceRefinementValue
  apply le_inf (bitsBelowValue_trans_r324 (h₂.trans inf_le_left) (h₁.trans inf_le_left))
  apply le_iInf
  intro m
  have hM := (faceRefinement_fixedMask_r327 h₁ m).trans
    (mask_under_r302 (outside_mask_antitone_r327 (h₁.trans inf_le_left) m)
      (faceRefinement_fixedMask_r327 h₂ m))
  exact (le_bitEq_iff_r126 _ _ _).mpr (by simpa only [inf_assoc] using hM)

end SetLanguage
end JSP000933
