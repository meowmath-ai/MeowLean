import JSP000930AnalyticEntireGrowth

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem complexBits_of_forcedName {n : ℕ} (v : DVec (V B) n) (Z : STerm n) (p : B)
    (h : p ≤ bTruth v (complex_f Z)) :
    ∃ a : ComplexBits B, a.CutOn p ∧ p ≤ bTerm v Z =ᴮ a.name := by
  let R : STerm (n+2) := realCoordinate_f
  let I : STerm (n+2) := imagCoordinate_f
  let D : SForm (n+2) := bd_and (realCut_f R) (bd_and (realCut_f I)
      (bd_and (bd_equal (up2 Z) (pair' R I)) (bd_equal R R)))
  let U : SForm (n+1) := sEx fun _ => D
  let F (x : bSet B) : B := bTruth (DVec.cons x v) U
  have hF : bSet.B_ext F := bTruth_body_ext_r191 v U
  have he : bTruth v (complex_f Z) = ⨆ x : bSet B,F x := by
    change bTruth v (sEx fun _ => U) = _
    rw [bTruth_sEx_r181]
  obtain ⟨x,hx⟩ := bSet.maximum_principle F hF
  have hX : p ≤ F x := h.trans (he.trans hx).le
  let vx : DVec (V B) (n+1) := DVec.cons x v
  let G (y : bSet B) : B := bTruth (DVec.cons y vx) D
  have hG : bSet.B_ext G := bTruth_body_ext_r191 vx D
  have hx' : F x = ⨆ y : bSet B,G y := by
    change bTruth vx (sEx fun _ => D) = _
    rw [bTruth_sEx_r181]
  obtain ⟨y,hy⟩ := bSet.maximum_principle G hG
  let V := complexCoordinates v x y
  have hV : p ≤ bTruth V D := hX.trans (hx'.trans hy).le
  simp only [D,bTruth_and_eq] at hV
  have hXR : p ≤ bTruth V (realCut_f R) := hV.trans inf_le_left
  have hYI : p ≤ bTruth V (realCut_f I) := hV.trans (inf_le_right.trans inf_le_left)
  have hXR' : bTerm V R = x := (bTerm_up_r181 vx y (bd_var ⟨0,Nat.succ_pos n⟩)).trans
    (bTerm_current_r181 v x)
  have hYI' : bTerm V I = y := bTerm_current_r181 vx y
  have hw : p ≤ bTerm v Z =ᴮ bSet.pair x y := by
    have hh : p ≤ bTruth V (bd_equal (up2 Z) (pair' R I)) :=
      hV.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hp : bTerm V (pair' R I) = bSet.pair x y :=
      (boolean_realize_bounded_term_pair' (v := V) R I).trans (congrArg₂ bSet.pair hXR' hYI')
    rw [bTruth_equal_r181,bTerm_up2_r181 v x y Z,hp] at hh
    exact hh
  let a : ComplexBits B := ⟨extractRationalWeights x,extractRationalWeights y⟩
  let xx := weightedRationalSet a.re
  let yy := weightedRationalSet a.im
  have hxx : p ≤ x =ᴮ xx := by
    simpa only [hXR',a,xx] using bTruth_realCut_recover V R p hXR
  have hyy : p ≤ y =ᴮ yy := by
    simpa only [hYI',a,yy] using bTruth_realCut_recover V I p hYI
  let VV := complexCoordinates v xx yy
  have hp1 : p ≤ bTruth VV (realCut_f R) :=
    (le_inf le_rfl hXR).trans ((bTruth_twoMask v x y xx yy (realCut_f R) p hxx hyy).le.trans inf_le_right)
  have hp2 : p ≤ bTruth VV (realCut_f I) :=
    (le_inf le_rfl hYI).trans ((bTruth_twoMask v x y xx yy (realCut_f I) p hxx hyy).le.trans inf_le_right)
  obtain ⟨hr,hi⟩ := forces_weightedComplex_coordinates v a.re a.im
  refine ⟨a,⟨(forces_realCut_weighted_iff VV R a.re hr p).1 hp1,
    (forces_realCut_weighted_iff VV I a.im hi p).1 hp2⟩,?_⟩
  exact bSet.bv_trans hw (bSet.pair_congr hxx hyy)

end JSP000930.AnalyticSyntax
