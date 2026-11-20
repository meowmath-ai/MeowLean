import JSP000933CountableBooleanAvoidance

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def independenceTest (K : Word × Word → B) (S : (ℕ → B) → B) : B :=
  ⨅ x : ℕ → B, ⨅ y : ℕ → B, (S x ⊓ S y)ᶜ ⊔ (colorValue K x y)ᶜ

noncomputable def qualifiedObstacle (K : Word × Word → B) (S : (ℕ → B) → B) (x : ℕ → B) : B :=
  independenceTest K S ⊓ S x

theorem qualifiedObstacle_independent_r141 (K : Word × Word → B) (S : (ℕ → B) → B)
    (p : B) (x y : ℕ → B) :
    Disjoint (p ⊓ (qualifiedObstacle K S x ⊓ qualifiedObstacle K S y)) (colorValue K x y) := by
  apply le_compl_iff_disjoint_right.mp
  let c := p ⊓ (qualifiedObstacle K S x ⊓ qualifiedObstacle K S y)
  have hI : c ≤ independenceTest K S :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hM : c ≤ S x ⊓ S y := le_inf (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have hImp : c ≤ (S x ⊓ S y)ᶜ ⊔ (colorValue K x y)ᶜ :=
    hI.trans ((iInf_le _ x).trans (iInf_le _ y))
  exact (le_inf le_rfl hM).trans ((le_materialImp_iff_r126 _ _ _).mp hImp)

theorem avoid_qualifiedObstacle_r141 (K : Word × Word → B) (S : (ℕ → B) → B)
    (p : B) (x : ℕ → B) (hp : p ≤ (qualifiedObstacle K S x)ᶜ) :
    p ⊓ independenceTest K S ≤ (S x)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  have hh : (p ⊓ independenceTest K S) ⊓ S x ≤ p ⊓ qualifiedObstacle K S x :=
    le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  exact hh.trans (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hp))

theorem equalitySingleton_independent_r141 (K : Word × Word → B) (p : B) (z : ℕ → B)
    (hirr : p ≤ (colorValue K z z)ᶜ) (x y : ℕ → B) :
    Disjoint (p ⊓ (realEqValue x z ⊓ realEqValue y z)) (colorValue K x y) := by
  apply disjoint_iff_inf_le.mpr
  let c := (p ⊓ (realEqValue x z ⊓ realEqValue y z)) ⊓ colorValue K x y
  have hEqX : c ≤ realEqValue x z :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hEqY : c ≤ realEqValue y z :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hm := mask_colorValue_congr_r127 K hEqX hEqY
  have hc : c ≤ colorValue K z z := (le_inf le_rfl inf_le_right).trans (hm.le.trans inf_le_right)
  have hnc : c ≤ (colorValue K z z)ᶜ := (inf_le_left.trans inf_le_left).trans hirr
  exact (le_inf hc hnc).trans_eq (inf_compl_eq_bot')

end CantorCodes
end JSP000933
