import JSP000933BooleanRealEquality

namespace JSP000933
namespace CantorCodes

open BooleanCompletion

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem mask_cylinder_congr_r127 {p : B} {x y : ℕ → B}
    (h : p ≤ realEqValue x y) (w : Word) :
    p ⊓ cylinderValue x w = p ⊓ cylinderValue y w := by
  apply mask_iInf_congr_r126
  intro i
  have he := (le_realEqValue_iff_r126 p x y).mp h i.val
  cases hw : w[i.val]
  · exact mask_compl_congr_r126 he
  · exact he

theorem mask_openValue_congr_r127 (code : Word → B) {p : B} {x y : ℕ → B}
    (h : p ≤ realEqValue x y) :
    p ⊓ openValue code x = p ⊓ openValue code y :=
  mask_iSup_congr_r126 (fun w => mask_inf_congr_r126 rfl (mask_cylinder_congr_r127 h w))

theorem mask_colorValue_congr_r127 (code : Word × Word → B) {p : B}
    {x x' y y' : ℕ → B} (hx : p ≤ realEqValue x x') (hy : p ≤ realEqValue y y') :
    p ⊓ colorValue code x y = p ⊓ colorValue code x' y' :=
  mask_iSup_congr_r126 (fun w => mask_inf_congr_r126 rfl
    (mask_inf_congr_r126 (mask_cylinder_congr_r127 hx w.1) (mask_cylinder_congr_r127 hy w.2)))

theorem realEqValue_refl_r127 (x : ℕ → B) : realEqValue x x = ⊤ :=
  top_unique ((le_realEqValue_iff_r126 ⊤ x x).mpr (fun _ => rfl))

theorem realEqValue_symm_r127 (x y : ℕ → B) : realEqValue x y = realEqValue y x := by
  unfold realEqValue
  apply congrArg (fun f : ℕ → B => iInf f)
  funext n
  unfold bitEq
  exact @inf_comm B _ ((x n)ᶜ ⊔ y n) ((y n)ᶜ ⊔ x n)

theorem realEqValue_trans_r127 (x y z : ℕ → B) :
    realEqValue x y ⊓ realEqValue y z ≤ realEqValue x z := by
  apply (le_realEqValue_iff_r126 (realEqValue x y ⊓ realEqValue y z) x z).mpr
  intro n
  exact ((le_realEqValue_iff_r126 _ x y).mp inf_le_left n).trans
    ((le_realEqValue_iff_r126 _ y z).mp inf_le_right n)

noncomputable def saturatedDomain (x : I → ℕ → B) (d : I → B) (r : ℕ → B) : B :=
  ⨆ i, d i ⊓ realEqValue r (x i)

theorem saturatedDomain_le_exact_r127 (x : I → ℕ → B) (d : I → B)
    (h : ∀ i j, d j ⊓ realEqValue (x i) (x j) ≤ d i) (i : I) :
    saturatedDomain x d (x i) = d i := by
  apply le_antisymm (iSup_le (h i))
  exact le_iSup_of_le i (by rw [realEqValue_refl_r127,inf_top_eq] <;> exact le_rfl)

theorem map_saturatedDomain_r127 (F : CompleteValueMap B C)
    (x : I → ℕ → B) (d : I → B) (r : ℕ → B) :
    F.toFun (saturatedDomain x d r) =
      saturatedDomain (fun i n => F.toFun (x i n)) (fun i => F.toFun (d i))
        (fun n => F.toFun (r n)) := by
  simp only [saturatedDomain,F.map_iSup,F.map_inf,map_realEqValue_r126]

end CantorCodes
end JSP000933
