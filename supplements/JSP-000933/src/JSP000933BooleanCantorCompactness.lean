import JSP000933ClosedPotentialTower

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_namedReal_allClosed_r225 (p : B) (s : Word) (K : ℕ → Word → B)
    (hP : p ≤ closedPotential K s) :
    ∃ x : ℕ → B, p ≤ cylinderValue x s ∧ ∀ n, p ≤ (openValue (K n) x)ᶜ := by
  classical
  obtain ⟨F⟩ := exists_closedPotentialTower_r224 p s K hP
  let x := F.limitBits
  refine ⟨x,?_,?_⟩
  · have h := F.weight_le_limitCylinder_r218 0 s
    simpa only [F.seed,seedWordPartition_weight_r217] using h
  · intro n
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    let q := p ⊓ openValue (K n) x
    change q ≤ ⊥
    by_contra hn
    have hq : q ≠ ⊥ := fun he => hn he.le
    obtain ⟨u,r,hr,hrq,hRu⟩ := exists_nonzero_below_choice_r135 q hq
      (fun u : Word => K n u ⊓ cylinderValue x u) inf_le_right
    let j := u.length+1
    have hrP : r ≤ p := hrq.trans inf_le_left
    have hrCover : r ≤ ⨆ w : Word, (F.level j).weight w := hrP.trans_eq (F.level j).covers.symm
    obtain ⟨w,t,ht,htr,htw⟩ := exists_nonzero_below_choice_r135 r hr (F.level j).weight hrCover
    have hLen : u.length ≤ w.length := by
      by_contra hle
      have he : (F.level j).weight w = ⊥ := F.lengthBound j w (by dsimp only [j]; omega)
      exact ht (le_bot_iff.mp (htw.trans_eq he))
    have hE : ExtendsWord u w :=
      extendsWord_of_compatible_r173 x ht hLen (htr.trans (hRu.trans inf_le_right))
        (htw.trans (F.weight_le_limitCylinder_r218 j w))
    have hPot : t ≤ closedPotentialAt K (n+1) w :=
      (htw.trans (F.code u.length w)).trans (iInf_le _ (n+1))
    obtain ⟨y,v,hv,hvt,hV⟩ := exists_nonzero_below_choice_r135 t ht
      (fun y : ℕ → B => cylinderValue y w ⊓ finiteClosedValue K (n+1) y) hPot
    have hOpen : v ≤ openValue (K n) y :=
      le_iSup_of_le u (le_inf
        (hvt.trans (htr.trans (hRu.trans inf_le_left)))
        (hV.trans (inf_le_left.trans (cylinderWord_mono_r173 y hE))))
    have hClosed : v ≤ (openValue (K n) y)ᶜ :=
      hV.trans (inf_le_right.trans (iInf_le _ (⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))))
    exact hv (le_bot_iff.mp ((le_inf hOpen hClosed).trans_eq inf_compl_eq_bot'))

end CantorCodes
end JSP000933
