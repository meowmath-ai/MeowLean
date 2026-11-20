import JSP000933ActualUniformApproximationValues

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualLongBlockLarge_ext_r314 : RealTestExt (actualLongBlockLarge (B := B)) := by
  intro p a b he
  unfold actualLongBlockLarge
  apply mask_iInf_congr_r126
  intro N
  apply mask_iSup_congr_r126
  intro i
  unfold actualIncludesBlock
  exact mask_iInf_congr_r126 (fun m => (le_realEqValue_iff_r126 _ _ _).mp he m.val)

theorem existsNamedUniformValue_cap_ext_r314 (F : (ℕ → B) → ℕ → B) (hF : NameMapExt F) (k : ℕ) :
    RealTestExt (fun c => existsNamedUniformValue F c k) := by
  intro p c d he
  unfold existsNamedUniformValue
  exact mask_iSup_congr_r126 (nameUniformWitnessValue_cap_mask_r313 F hF he k)

noncomputable def largeUniformCapValue (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ) (d : ℕ → B) : B :=
  bitsBelowValue d c⊓(actualLongBlockLarge d⊓existsNamedUniformValue F d k)

noncomputable def existsLargeUniformCapValue (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ) : B :=
  ⨆ d : ℕ → B, largeUniformCapValue F c k d

theorem largeUniformCapValue_ext_r314 (F : (ℕ → B) → ℕ → B) (hF : NameMapExt F) (c : ℕ → B) (k : ℕ) :
    RealTestExt (largeUniformCapValue F c k) := by
  intro p a b he
  exact mask_inf_congr_r126 (bitsBelowValue_mask_r256 he (le_top.trans_eq (realEqValue_refl_r127 c).symm))
    (mask_inf_congr_r126 (actualLongBlockLarge_ext_r314 p a b he)
      (existsNamedUniformValue_cap_ext_r314 F hF k p a b he))

theorem existsLargeUniformCapValue_elim_r314 (F : (ℕ → B) → ℕ → B) (hF : NameMapExt F) (c : ℕ → B)
    (k : ℕ) {p : B} (h : p≤existsLargeUniformCapValue F c k) :
    ∃ d : ℕ → B, p≤bitsBelowValue d c ∧ p≤actualLongBlockLarge d ∧
      ∃ f : (ℕ → B) → ℕ → B, NamedContinuousOn p f ∧ p≤uniformTailErrorValue F d k f := by
  obtain ⟨d,hd⟩ := exists_realName_maximum_r138 (largeUniformCapValue F c k)
    (largeUniformCapValue_ext_r314 F hF c k) p h
  exact ⟨d,hd.trans inf_le_left,hd.trans (inf_le_right.trans inf_le_left),
    existsNamedUniformValue_elim_r313 F d k (hd.trans (inf_le_right.trans inf_le_right))⟩

theorem NamedContinuousOn.restrict_r314 {p q : B} {f : (ℕ → B) → ℕ → B} (h : NamedContinuousOn p f)
    (hq : q≤p) : NamedContinuousOn q f :=
  fun x N r hr hrq => h x N r hr (hrq.trans hq)

end SetLanguage
end JSP000933
