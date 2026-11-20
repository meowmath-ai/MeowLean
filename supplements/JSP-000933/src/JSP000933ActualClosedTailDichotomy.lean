import JSP000933ActualRelativeCantorBaire

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def goodTailInteriorValue (K : ℕ → Word → B) (s : Word) : B :=
  ⨆ N : ℕ, ⨆ u : {u : Word // ExtendsWord s u}, cylinderInClosedValue (K N) u.val

noncomputable def robustGoodTails (K : ℕ → Word → B) : B :=
  ⨅ s : Word, goodTailInteriorValue K s

theorem noGoodInterior_relativeDense_r304 (K : ℕ → Word → B) (s : Word)
    {p : B} (hp : p≤(goodTailInteriorValue K s)ᶜ) (N : ℕ) :
    DenseWithinCylinder p s (K N) := by
  intro u hu
  have hU : cylinderInClosedValue (K N) u≤goodTailInteriorValue K s :=
    le_iSup_of_le N (le_iSup (fun v : {v : Word // ExtendsWord s v} =>
      cylinderInClosedValue (K N) v.val) ⟨u,hu⟩)
  exact (hp.trans (compl_le_compl hU)).trans_eq (cylinderInClosedValue_compl_r220 (K N) u)

theorem cylinder_closedCover_has_interior_r304 (K : ℕ → Word → B) (s : Word)
    {p : B} (h : ∀ x : ℕ → B, p⊓cylinderValue x s≤⨆ N, (openValue (K N) x)ᶜ) :
    p≤goodTailInteriorValue K s := by
  let V := goodTailInteriorValue K s
  let q := p⊓Vᶜ
  have hq : q≤⊥ := by
    by_contra hn
    have hN : q≠⊥ := fun he => hn he.le
    obtain ⟨x,hS,hAll⟩ := exists_name_meeting_relative_dense_r303 q s K
      (noGoodInterior_relativeDense_r304 K s (show q≤Vᶜ from inf_le_right))
    have hv : q≤⨆ N, (openValue (K N) x)ᶜ :=
      (le_inf inf_le_left hS).trans (h x)
    have hC : q≤(⨆ N, (openValue (K N) x)ᶜ)ᶜ := by
      rw [compl_iSup]
      simpa only [compl_compl] using (le_iInf hAll)
    exact hN (le_bot_iff.mp ((le_inf hv hC).trans_eq inf_compl_eq_bot'))
  exact (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hq)).trans_eq (compl_compl V)

theorem not_robustGoodTails_has_bad_cylinder_r304 (K : ℕ → Word → B) {p : B}
    (hp : p≠⊥) (h : p≤(robustGoodTails K)ᶜ) :
    ∃ (q : B) (s : Word), q≠⊥ ∧ q≤p ∧ ∀ N, DenseWithinCylinder q s (K N) := by
  unfold robustGoodTails at h
  rw [compl_iInf] at h
  obtain ⟨s,q,hq,hqp,hS⟩ := exists_nonzero_below_choice_r135 p hp (fun s => (goodTailInteriorValue K s)ᶜ) h
  exact ⟨q,s,hq,hqp,noGoodInterior_relativeDense_r304 K s hS⟩

end SetLanguage
end JSP000933
