import JSP000933BooleanOpenCodeDensity

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def cylinderInClosedValue (K : Word → B) (u : Word) : B :=
  ⨅ x : ℕ → B, (cylinderValue x u)ᶜ ⊔ (openValue K x)ᶜ

noncomputable def fullClosedCoverValue (K : ℕ → Word → B) : B :=
  ⨅ x : ℕ → B, ⨆ n : ℕ, (openValue (K n) x)ᶜ

theorem cylinderInClosedValue_compl_r220 (K : Word → B) (u : Word) :
    (cylinderInClosedValue K u)ᶜ = ⨆ x : ℕ → B, cylinderValue x u ⊓ openValue K x := by
  simp only [cylinderInClosedValue,compl_iInf,compl_sup,compl_compl]

theorem fullClosedCover_has_cylinder_r220 (K : ℕ → Word → B) :
    fullClosedCoverValue K ≤ ⨆ n : ℕ, ⨆ u : Word, cylinderInClosedValue (K n) u := by
  classical
  apply le_of_dense_named_refinements_r219
  intro p hp hCover
  let V := ⨆ n : ℕ, ⨆ u : Word, cylinderInClosedValue (K n) u
  by_contra hn
  have hd : ∀ n, DenseOpenNaming p (K n) := by
    intro n u
    have hUV : cylinderInClosedValue (K n) u ≤ V :=
      le_iSup_of_le n (le_iSup _ u)
    have hZ : p ⊓ cylinderInClosedValue (K n) u = ⊥ := by
      by_contra hz
      exact hn ⟨p ⊓ cylinderInClosedValue (K n) u,hz,inf_le_left,inf_le_right.trans hUV⟩
    exact ((le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hZ.le)).trans_eq
      (cylinderInClosedValue_compl_r220 (K n) u))
  obtain ⟨x,_,hAll⟩ := exists_namedReal_meeting_denseOpen_r219 p [] K hd
  let covered := ⨆ n : ℕ, (openValue (K n) x)ᶜ
  have hr : p ≤ covered := hCover.trans (iInf_le _ x)
  have hc : p ≤ coveredᶜ := by
    unfold covered
    rw [compl_iSup]
    simpa only [compl_compl] using (le_iInf hAll)
  exact hp (le_bot_iff.mp ((le_inf hr hc).trans_eq (inf_compl_eq_bot' (x := covered))))

end CantorCodes
end JSP000933
