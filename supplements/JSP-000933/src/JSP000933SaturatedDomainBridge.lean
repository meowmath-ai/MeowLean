import JSP000933QualifiedIndependentObstacles

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem mask_realEq_congr_r142 {p : B} {x y : ℕ → B}
    (h : p ≤ realEqValue x y) (z : ℕ → B) :
    p ⊓ realEqValue x z = p ⊓ realEqValue y z := by
  apply le_antisymm
  · apply le_inf inf_le_left
    exact (le_inf (inf_le_left.trans (h.trans_eq (realEqValue_symm_r127 x y))) inf_le_right).trans
      (realEqValue_trans_r127 y x z)
  · apply le_inf inf_le_left
    exact (le_inf (inf_le_left.trans h) inf_le_right).trans (realEqValue_trans_r127 x y z)

theorem saturatedDomain_ext_r142 (x : I → ℕ → B) (d : I → B) :
    RealTestExt (saturatedDomain x d) :=
  fun _ _ _ he => mask_iSup_congr_r126
    (fun i => mask_inf_congr_r126 rfl (mask_realEq_congr_r142 he (x i)))

theorem le_saturatedDomain_at_index_r142 (x : I → ℕ → B) (d : I → B) (i : I) :
    d i ≤ saturatedDomain x d (x i) :=
  le_iSup_of_le i (by rw [realEqValue_refl_r127,inf_top_eq] <;> exact le_rfl)

theorem goodCover_saturation_le_indexed_r142
    (x : I → ℕ → B) (d : I → B) (K : Word × Word → B) (c : CoverCode B) :
    goodCoverValue id (saturatedDomain x d) K c ≤ goodCoverValue x d K c := by
  apply inf_le_inf
  · apply le_iInf
    intro i
    have hit := iInf_le (fun y : ℕ → B =>
      (saturatedDomain x d y)ᶜ ⊔ (⨆ n, ClosedMember c n y)) (x i)
    exact hit.trans (sup_le_sup_right (compl_le_compl (le_saturatedDomain_at_index_r142 x d i)) _)
  · apply le_iInf
    intro a
    let q : ℕ × (ℕ → B) × (ℕ → B) := (a.1,x a.2.1,x a.2.2)
    have hh := iInf_le (fun b : ℕ × (ℕ → B) × (ℕ → B) =>
      ((saturatedDomain x d b.2.1 ⊓ saturatedDomain x d b.2.2) ⊓
        (ClosedMember c b.1 b.2.1 ⊓ ClosedMember c b.1 b.2.2))ᶜ
        ⊔ (colorValue K b.2.1 b.2.2)ᶜ) q
    exact hh.trans (sup_le_sup_right (compl_le_compl (inf_le_inf_right _
      (inf_le_inf (le_saturatedDomain_at_index_r142 x d a.2.1)
        (le_saturatedDomain_at_index_r142 x d a.2.2)))) _)

theorem noCover_saturation_r142
    (x : I → ℕ → B) (d : I → B) (K : Word × Word → B) (p : B)
    (h : ∀ c : CoverCode B, p ≤ (goodCoverValue x d K c)ᶜ) :
    ∀ c : CoverCode B, p ≤ (goodCoverValue id (saturatedDomain x d) K c)ᶜ :=
  fun c => (h c).trans (compl_le_compl (goodCover_saturation_le_indexed_r142 x d K c))

end CantorCodes
end JSP000933
