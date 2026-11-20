import JSP000933SimultaneousFiniteFeasibility

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem DecidesOnCylinder.mask_eq_r286 {p r : B} {u : Word} {x y : ℕ → B} {f : (ℕ → B) → B}
    (h : DecidesOnCylinder p u f) (hr : r≤p)
    (hx : r≤cylinderValue x u) (hy : r≤cylinderValue y u) :
    r⊓f x=r⊓f y := by
  rcases h with h | h
  · exact (inf_eq_left.mpr (h x r hr hx)).trans (inf_eq_left.mpr (h y r hr hy)).symm
  · have hX : r⊓f x=⊥ :=
      le_bot_iff.mp (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp (h x r hr hx)))
    have hY : r⊓f y=⊥ :=
      le_bot_iff.mp (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp (h y r hr hy)))
    exact hX.trans hY.symm

noncomputable def actualLexRegularValue (K : Word × Word → B) (x : ℕ → B) : B :=
  ⨅ s : Word, openValue (closedBoundaryRegularCode (projectedFailureCode K s)) x

theorem actualLexSelector_regular_prefix_r286 (K : Word × Word → B) (x : ℕ → B)
    (N : ℕ) {p : B} (hp : p≠⊥) (hR : p≤actualLexRegularValue K x) :
    ∃ (q : B) (u : Word), q≠⊥ ∧ q≤p ∧ q≤cylinderValue x u ∧
      ∀ (y : ℕ → B) (r : B), r≤q → r≤cylinderValue y u →
        ∀ m<N, r⊓actualLexSelector K x m=r⊓actualLexSelector K y m := by
  obtain ⟨q,u,hq,hqp,hX,hDec⟩ := finiteFeasibleTests_sameCylinder_r285 K x (boundedWordFinset N) p hp
    (fun s _ => hR.trans (iInf_le _ s))
  refine ⟨q,u,hq,hqp,hX,fun y r hr hY => ?_⟩
  apply actualLexSelector_maskFirst_r284 K N
  intro s hs
  exact (hDec s ((mem_boundedWordFinset_r285 N s).mpr hs)).mask_eq_r286 hr (hr.trans hX) hY

end SetLanguage
end JSP000933
