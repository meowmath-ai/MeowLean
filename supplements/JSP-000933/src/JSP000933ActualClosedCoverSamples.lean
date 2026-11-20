import JSP000933ActualConcreteCrossingCover

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def closedSampleTest (D : (ℕ → B) → B) (C : CoverCode B) (n : ℕ) (u : Word) (x : ℕ → B) : B :=
  D x ⊓ (ClosedMember C n x ⊓ cylinderValue x u)

theorem closedSampleTest_ext_r261 (D : (ℕ → B) → B) (hD : RealTestExt D)
    (C : CoverCode B) (n : ℕ) (u : Word) : RealTestExt (closedSampleTest D C n u) := by
  intro p x y h
  exact mask_inf_congr_r126 (hD p x y h) (mask_inf_congr_r126
    (mask_compl_congr_r126 (mask_openValue_congr_r127 (C n) h)) (mask_cylinder_congr_r127 h u))

noncomputable def closedSamplePresent (D : (ℕ → B) → B) (C : CoverCode B) (n : ℕ) (u : Word) : B :=
  ⨆ x : ℕ → B, closedSampleTest D C n u x

structure ClosedCoverSamples (D : (ℕ → B) → B) (C : CoverCode B) (p : B) where
  nameFor : ℕ → Word → ℕ → B
  qualified : ∀ n u, p ⊓ closedSamplePresent D C n u ≤ closedSampleTest D C n u (nameFor n u)

theorem closedCover_has_actualSamples_r261 (D : (ℕ → B) → B) (hD : RealTestExt D)
    (C : CoverCode B) (p : B) : Nonempty (ClosedCoverSamples D C p) := by
  classical
  have he (n : ℕ) (u : Word) : ∃ x : ℕ → B,
      p ⊓ closedSamplePresent D C n u ≤ closedSampleTest D C n u x :=
    exists_realName_maximum_r138 _ (closedSampleTest_ext_r261 D hD C n u) _ inf_le_right
  choose S hS using he
  exact ⟨⟨S,hS⟩⟩

theorem ClosedCoverSamples.matches_r261 {D : (ℕ → B) → B} {C : CoverCode B} {p q : B}
    (S : ClosedCoverSamples D C p) (hq : q≤p) (n : ℕ) (u : Word) (x : ℕ → B)
    (hX : q≤D x) (hC : q≤ClosedMember C n x) (hU : q≤cylinderValue x u) :
    q≤closedSampleTest D C n u (S.nameFor n u) :=
  (le_inf hq (le_iSup_of_le x (le_inf hX (le_inf hC hU)))).trans (S.qualified n u)

theorem sameCylinder_mask_r261 {q : B} {x y : ℕ → B} {u : Word}
    (hx : q≤cylinderValue x u) (hy : q≤cylinderValue y u) (m : ℕ) (hm : m<u.length) :
    q⊓x m = q⊓y m :=
  (cylinder_fixes_paddedBits_r258 hx m hm).trans (cylinder_fixes_paddedBits_r258 hy m hm).symm

theorem ClosedCoverSamples.samePrefix_r261 {D : (ℕ → B) → B} {C : CoverCode B} {p q : B}
    (S : ClosedCoverSamples D C p) (hq : q≤p) (n : ℕ) (u : Word) (x : ℕ → B)
    (hX : q≤D x) (hC : q≤ClosedMember C n x) (hU : q≤cylinderValue x u)
    (m : ℕ) (hm : m<u.length) : q⊓x m=q⊓S.nameFor n u m :=
  sameCylinder_mask_r261 hU
    ((S.matches_r261 hq n u x hX hC hU).trans (inf_le_right.trans inf_le_right)) m hm

theorem goodCover_independent_on_r261 {D : (ℕ → B) → B} {K : Word × Word → B}
    {C : CoverCode B} {p : B} (h : p≤goodCoverValue id D K C) (n : ℕ) (x y : ℕ → B)
    (hx : p≤D x) (hy : p≤D y) (hcX : p≤ClosedMember C n x) (hcY : p≤ClosedMember C n y) :
    p≤(colorValue K x y)ᶜ := by
  have hI : p≤((D x ⊓ D y) ⊓ (ClosedMember C n x ⊓ ClosedMember C n y))ᶜ ⊔
      (colorValue K x y)ᶜ := h.trans (inf_le_right.trans (iInf_le _ (n,x,y)))
  exact ((le_inf le_rfl (le_inf (le_inf hx hy) (le_inf hcX hcY))).trans
    ((le_materialImp_iff_r126 _ _ _).mp hI))

end SetLanguage
end JSP000933
