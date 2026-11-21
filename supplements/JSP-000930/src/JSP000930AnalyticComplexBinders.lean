import JSP000930AnalyticComplexPair
import JSP000930AnalyticMulCutClosure

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_oneMask {n : ℕ} (v : DVec (V B) n) (x y : bSet B) (φ : SForm (n+1)) (p : B)
    (h : p ≤ x =ᴮ y) :
    p ⊓ bTruth (DVec.cons x v) φ = p ⊓ bTruth (DVec.cons y v) φ := by
  apply bTruth_vecMask_r191
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h
  · exact bSet.bv_refl

theorem bTruth_twoMask {n : ℕ} (v : DVec (V B) n) (x y a b : bSet B) (φ : SForm (n+2)) (p : B)
    (hx : p ≤ x =ᴮ a) (hy : p ≤ y =ᴮ b) :
    p ⊓ bTruth (complexCoordinates v x y) φ = p ⊓ bTruth (complexCoordinates v a b) φ := by
  apply bTruth_vecMask_r191
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hy
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact hx
    · exact bSet.bv_refl

theorem bTruth_unpackComplex_pair {n k : ℕ} (v : DVec (V B) n)
    (z : STerm n) (ps : Fin k → STerm n)
    (body : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → SForm d)
    (a b : bSet B) (hz : bTerm v z = bSet.pair a b) :
    let Vab := complexCoordinates v a b
    let X : STerm (n+2) := realCoordinate_f
    let Y : STerm (n+2) := imagCoordinate_f
    bTruth v (unpackComplex_f z ps body) =
      bTruth Vab (bd_and (realCut_f X) (bd_and (realCut_f Y)
        (body (fun i => up2 (ps i)) X Y))) := by
  let X : STerm (n+2) := realCoordinate_f
  let Y : STerm (n+2) := imagCoordinate_f
  let ψ : SForm (n+2) := bd_and (realCut_f X)
    (bd_and (realCut_f Y) (body (fun i => up2 (ps i)) X Y))
  let Vxy (x y : bSet B) := complexCoordinates v x y
  have hEq (x y : bSet B) :
      bTruth (Vxy x y) (bd_equal (up2 z) (pair' X Y)) =
        ((a =ᴮ x) ⊓ (b =ᴮ y)) := by
    have hz' : bTerm (Vxy x y) (up2 z) = bSet.pair a b :=
      (bTerm_up2_r181 v x y z).trans hz
    have hp : bTerm (Vxy x y) (pair' X Y) = bSet.pair x y :=
      boolean_realize_bounded_term_pair' (v := Vxy x y) X Y
    change (bTerm (Vxy x y) (up2 z) =ᴮ bTerm (Vxy x y) (pair' X Y)) = _
    rw [hz',hp,pair_eq_inf_r189]
  change bTruth v (unpackComplex_f z ps body) = bTruth (Vxy a b) ψ
  simp only [unpackComplex_f,bTruth_sEx_r181]
  change (⨆ x : bSet B, ⨆ y : bSet B, bTruth (Vxy x y)
    (bd_and (bd_equal (up2 z) (pair' X Y)) ψ)) = _
  simp only [boolean_realize_bounded_formula_and,hEq]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun y => ?_
    rw [bTruth_twoMask v x y a b ψ ((a =ᴮ x) ⊓ (b =ᴮ y))
      (inf_le_left.trans_eq bSet.bv_eq_symm)
      (inf_le_right.trans_eq bSet.bv_eq_symm)]
    exact inf_le_right
  · refine le_iSup_of_le a (le_iSup_of_le b ?_)
    change bTruth (Vxy a b) ψ ≤ ((a =ᴮ a) ⊓ (b =ᴮ b)) ⊓ bTruth (Vxy a b) ψ
    simp only [show (a =ᴮ a) = (⊤ : B) from top_unique bSet.bv_refl,
      show (b =ᴮ b) = (⊤ : B) from top_unique bSet.bv_refl, top_inf_eq]
    exact le_rfl

theorem bTruth_selectReal_weighted {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (R D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (w : RatPresentation → B) (p : B)
    (hw : ProperCutOn p w)
    (hR : ∀ u : RatPresentation → B,
      let a := weightedRationalSet u
      let Va := DVec.cons a v
      let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
      bTruth Va (R (fun i => up (ps i)) T) = (a =ᴮ weightedRationalSet w)) :
    let Vw := DVec.cons (weightedRationalSet w) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps R D) =
      p ⊓ bTruth Vw (D (fun i => up (ps i)) T) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Vx (x : bSet B) := DVec.cons x v
  let φ := R (fun i => up (ps i)) T
  let ψ := D (fun i => up (ps i)) T
  let W := weightedRationalSet w
  change p ⊓ bTruth v (selectReal_f ps R D) = p ⊓ bTruth (Vx W) ψ
  simp only [selectReal_f,bTruth_sEx_r181,boolean_realize_bounded_formula_and]
  change (p ⊓ (⨆ x : bSet B, bTruth (Vx x) (realCut_f T) ⊓
    (bTruth (Vx x) φ ⊓ bTruth (Vx x) ψ))) = _
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    let e := p ⊓ (bTruth (Vx x) (realCut_f T) ⊓ (bTruth (Vx x) φ ⊓ bTruth (Vx x) ψ))
    change e ≤ _
    have hep : e ≤ p := inf_le_left
    have hcut : e ≤ bTruth (Vx x) (realCut_f T) := inf_le_right.trans inf_le_left
    have hφ : e ≤ bTruth (Vx x) φ := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hψ : e ≤ bTruth (Vx x) ψ := inf_le_right.trans (inf_le_right.trans inf_le_right)
    let u := extractRationalWeights x
    have he : e ≤ x =ᴮ weightedRationalSet u := by
      have he' := bTruth_realCut_recover (Vx x) T e hcut
      exact he'
    have he' : e ≤ weightedRationalSet u =ᴮ W := by
      rw [← hR u]
      exact (le_inf le_rfl hφ).trans ((bTruth_oneMask v x (weightedRationalSet u) φ e he).le.trans inf_le_right)
    have hxW : e ≤ x =ᴮ W :=
      bSet.bv_trans he he'
    exact le_inf hep ((le_inf le_rfl hψ).trans
      ((bTruth_oneMask v x W ψ e hxW).le.trans inf_le_right))
  · refine le_iSup_of_le W ?_
    have hc : p ≤ bTruth (Vx W) (realCut_f T) :=
      (forces_realCut_weighted_iff (Vx W) T w (bTerm_current_r181 v W) p).2 hw
    have hφ : bTruth (Vx W) φ = (⊤ : B) :=
      (hR w).trans (top_unique bSet.bv_refl)
    rw [hφ,top_inf_eq]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hc) inf_le_right)

end JSP000930.AnalyticSyntax
