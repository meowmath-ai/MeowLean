import JSP000930AnalyticSentence
import JSP000930AnalyticValidCutBridge

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev complexCoordinates {n : ℕ} (v : DVec (V B) n) (re im : bSet B) :
    DVec (V B) (n+2) := DVec.cons im (DVec.cons re v)

def realCoordinate_f {n : ℕ} : STerm (n+2) :=
  up ((bd_var ⟨0,Nat.succ_pos n⟩) : STerm (n+1))

def imagCoordinate_f {n : ℕ} : STerm (n+2) :=
  bd_var ⟨0,Nat.succ_pos (n+1)⟩

theorem bTruth_complex_expand {n : ℕ} (v : DVec (V B) n) (Z : STerm n) :
    bTruth v (complex_f Z) =
      ⨆ x : bSet B, ⨆ y : bSet B,
        (bTruth (complexCoordinates v x y) (realCut_f realCoordinate_f) ⊓
          bTruth (complexCoordinates v x y) (realCut_f imagCoordinate_f)) ⊓
            (bTerm v Z =ᴮ bSet.pair x y) := by
  change bTruth v (sEx fun x => sEx fun y =>
    bd_and (realCut_f (up x)) (bd_and (realCut_f y)
      (bd_and (bd_equal (up2 Z) (pair' (up x) y)) (bd_equal (up x) (up x))))) = _
  simp only [bTruth_sEx_r181, boolean_realize_bounded_formula_and,
    bTruth_equal_r181, boolean_realize_bounded_term_pair',
    bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,
    complexCoordinates,realCoordinate_f,imagCoordinate_f]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro y
  let u : DVec (V B) (n+2) := DVec.cons y (DVec.cons x v)
  let a : STerm (n+1) := bd_var ⟨0, Nat.succ_pos n⟩
  let b : STerm (n+2) := bd_var ⟨0, Nat.succ_pos (n+1)⟩
  have ha : bTerm u (up a) = x :=
    (bTerm_up_r181 (DVec.cons x v) y a).trans (bTerm_current_r181 v x)
  have hb : bTerm u b = y := bTerm_current_r181 (DVec.cons x v) y
  have hZ : bTerm u (up2 Z) = bTerm v Z := bTerm_up2_r181 v x y Z
  have hp : bTerm u (pair' (up a) b) = bSet.pair (bTerm u (up a)) (bTerm u b) :=
    boolean_realize_bounded_term_pair' (v := u) (up a) b
  change bTruth u (realCut_f (up a)) ⊓ (bTruth u (realCut_f b) ⊓
    ((bTerm u (up2 Z) =ᴮ bTerm u (pair' (up a) b)) ⊓ (bTerm u (up a) =ᴮ bTerm u (up a)))) = _
  rw [hp, ha, hb, hZ, show (x =ᴮ x) = (⊤ : B) from top_unique bSet.bv_refl, inf_top_eq, inf_assoc]

theorem forces_complex_pair_of_weightedCuts {n : ℕ} (v : DVec (V B) n) (Z : STerm n)
    (re im : RatPresentation → B) (p : B)
    (hZ : p ≤ bTerm v Z =ᴮ bSet.pair (weightedRationalSet re) (weightedRationalSet im))
    (hre : let w := complexCoordinates v (weightedRationalSet re) (weightedRationalSet im)
      p ≤ bTruth w (realCut_f realCoordinate_f))
    (him : let w := complexCoordinates v (weightedRationalSet re) (weightedRationalSet im)
      p ≤ bTruth w (realCut_f imagCoordinate_f)) :
    p ≤ bTruth v (complex_f Z) := by
  rw [bTruth_complex_expand]
  exact ((le_inf (le_inf hre him) hZ).trans
    (le_iSup_of_le (weightedRationalSet re) (le_iSup (fun y : bSet B =>
      (bTruth (complexCoordinates v (weightedRationalSet re) y) (realCut_f realCoordinate_f) ⊓
       bTruth (complexCoordinates v (weightedRationalSet re) y) (realCut_f imagCoordinate_f)) ⊓
       (bTerm v Z =ᴮ bSet.pair (weightedRationalSet re) y)) (weightedRationalSet im))))

theorem forces_weightedComplex_coordinates {n : ℕ} (v : DVec (V B) n)
    (re im : RatPresentation → B) :
    let w := complexCoordinates v (weightedRationalSet re) (weightedRationalSet im)
    (bTerm w realCoordinate_f = weightedRationalSet re) ∧
      (bTerm w imagCoordinate_f = weightedRationalSet im) := by
  exact ⟨(bTerm_up_r181 (DVec.cons (weightedRationalSet re) v)
      (weightedRationalSet im) (bd_var ⟨0,Nat.succ_pos n⟩)).trans
      (bTerm_current_r181 v (weightedRationalSet re)),
    bTerm_current_r181 (DVec.cons (weightedRationalSet re) v) (weightedRationalSet im)⟩

theorem complex_local_representation {n : ℕ} (v : DVec (V B) n) (Z : STerm n) (p : B)
    (hp : p ≤ bTruth v (complex_f Z)) :
    p = ⨆ x : bSet B, ⨆ y : bSet B, p ⊓
      ((bTruth (complexCoordinates v x y) (realCut_f realCoordinate_f) ⊓
        bTruth (complexCoordinates v x y) (realCut_f imagCoordinate_f)) ⊓
          (bTerm v Z =ᴮ bSet.pair x y)) := by
  simp only [← inf_iSup_eq]
  rw [← bTruth_complex_expand v Z]
  exact (inf_eq_left.mpr hp).symm

end JSP000930.AnalyticSyntax
