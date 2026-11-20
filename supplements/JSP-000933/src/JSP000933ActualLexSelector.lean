import JSP000933ActualLexicographicTower

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualLexSelector_closed_r284 (K : Word × Word → B) (x : ℕ → B) :
    actualFiberFeasible K x []≤(colorValue K x (actualLexSelector K x))ᶜ := by
  let P := actualFiberFeasible K x []
  let F := actualLexTower K x
  let y := actualLexSelector K x
  let O := rightSectionOpenCode K x
  rw [← rightSectionOpenCode_value_r276]
  change P≤(openValue O y)ᶜ
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  let q := P⊓openValue O y
  change q≤⊥
  by_contra hn
  have hq : q≠⊥ := fun he => hn he.le
  obtain ⟨u,r,hr,hrq,hRu⟩ := exists_nonzero_below_choice_r135 q hq
    (fun u : Word => O u⊓cylinderValue y u) inf_le_right
  let j := u.length+1
  have hrP : r≤P := hrq.trans inf_le_left
  have hrCover : r≤⨆ w : Word, (F.level j).weight w := hrP.trans_eq (F.level j).covers.symm
  obtain ⟨w,t,ht,htr,htw⟩ := exists_nonzero_below_choice_r135 r hr (F.level j).weight hrCover
  have hLen : u.length≤w.length := by
    by_contra hle
    have he : (F.level j).weight w=⊥ := F.lengthBound j w (by dsimp only [j]; omega)
    exact ht (le_bot_iff.mp (htw.trans_eq he))
  have hE : ExtendsWord u w :=
    extendsWord_of_compatible_r173 y ht hLen (htr.trans (hRu.trans inf_le_right))
      (htw.trans (F.weight_le_limitCylinder_r218 j w))
  have hPot : t≤actualFiberFeasible K x w := htw.trans (F.code u.length w)
  obtain ⟨z,v,hv,hvt,hV⟩ := exists_nonzero_below_choice_r135 t ht
    (fun z : ℕ → B => cylinderValue z w⊓(colorValue K x z)ᶜ) hPot
  have hOpen : v≤openValue O z :=
    le_iSup_of_le u (le_inf
      (hvt.trans (htr.trans (hRu.trans inf_le_left)))
      (hV.trans (inf_le_left.trans (cylinderWord_mono_r173 z hE))))
  have hClosed : v≤(openValue O z)ᶜ :=
    (hV.trans inf_le_right).trans_eq
      (congrArg (fun b : B => bᶜ) (rightSectionOpenCode_value_r276 K x z).symm)
  exact hv (le_bot_iff.mp ((le_inf hOpen hClosed).trans_eq inf_compl_eq_bot'))

theorem actualLexSelector_maskFirst_r284 (K : Word × Word → B) {p : B} {x y : ℕ → B} (N : ℕ)
    (hFeas : ∀ s, s.length≤N → p⊓actualFiberFeasible K x s=p⊓actualFiberFeasible K y s) :
    ∀ m<N, p⊓actualLexSelector K x m=p⊓actualLexSelector K y m := by
  intro m hm
  unfold actualLexSelector WordPartitionTower.limitBits
  apply mask_iSup_congr_r126
  intro u
  change p⊓lexAtWeight (actualFiberFeasible K x) (m+1) u.val =
    p⊓lexAtWeight (actualFiberFeasible K y) (m+1) u.val
  by_cases hu : u.val.length=m+1
  · simp only [lexAtWeight,ite_eq_left hu]
    exact namedLexWordWeight_mask_r281 p N hFeas u.val (hu.trans_le (Nat.succ_le_of_lt hm))
  · simp only [lexAtWeight,ite_eq_right hu]

end SetLanguage
end JSP000933
