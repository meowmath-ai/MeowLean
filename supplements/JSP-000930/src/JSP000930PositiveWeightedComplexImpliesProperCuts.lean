import JSP000930PositiveActualNamedTaylorGap
import JSP000930AnalyticComplexPair

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem properCutOn_mono {β : RatPresentation → B} {p q : B}
    (hq : q ≤ p) (h : ProperCutOn p β) : ProperCutOn q β := by
  obtain ⟨a,b,c,d⟩ := h
  exact ⟨hq.trans a,hq.trans b,fun r s hrs => (inf_le_inf_right _ hq).trans (c r s hrs),
    fun r => (inf_le_inf_right _ hq).trans (d r)⟩

theorem properCutOn_iSup {I : Sort*} {β : RatPresentation → B} (p : I → B)
    (h : ∀ i,ProperCutOn (p i) β) : ProperCutOn (⨆ i,p i) β := by
  refine ⟨iSup_le (fun i => (h i).1),iSup_le (fun i => (h i).2.1),?_,?_⟩
  · intro r s hrs
    rw [iSup_inf_eq]
    exact iSup_le fun i => (h i).2.2.1 r s hrs
  · intro r
    rw [iSup_inf_eq]
    exact iSup_le fun i => (h i).2.2.2 r

theorem properCutOn_of_weighted_complex {n : ℕ}
    (v : DVec (V B) n) (Z : STerm n) (U W : RatPresentation → B) (p : B)
    (hZ : p ≤ bTerm v Z =ᴮ pair (weightedRationalSet U) (weightedRationalSet W))
    (hC : p ≤ bTruth v (complex_f Z)) :
    ProperCutOn p U ∧ ProperCutOn p W := by
  let cell (x y : bSet B) : B := p ⊓
    ((bTruth (complexCoordinates v x y) (realCut_f realCoordinate_f) ⊓
      bTruth (complexCoordinates v x y) (realCut_f imagCoordinate_f)) ⊓
      (bTerm v Z =ᴮ pair x y))
  have hCover : p = ⨆ x : bSet B,⨆ y : bSet B,cell x y :=
    complex_local_representation v Z p hC
  have hCell (x y : bSet B) : ProperCutOn (cell x y) U ∧ ProperCutOn (cell x y) W := by
    let c := cell x y
    let a := weightedRationalSet U
    let b := weightedRationalSet W
    let s := complexCoordinates v x y
    let t := complexCoordinates v a b
    have hP : c ≤ pair x y =ᴮ pair a b :=
      bv_trans (bv_symm (inf_le_right.trans inf_le_right)) (inf_le_left.trans hZ)
    have hx : c ≤ x =ᴮ a := hP.trans eq_of_eq_pair_left
    have hy : c ≤ y =ᴮ b := hP.trans eq_of_eq_pair_right
    have hVec : ∀ i : Fin (n+2),c ≤ s.nth i.val i.isLt =ᴮ t.nth i.val i.isLt := by
      intro i
      refine Fin.cases hy (fun j => ?_) i
      exact Fin.cases hx (fun _ => bv_refl) j
    have hReal : c ≤ bTruth t (realCut_f realCoordinate_f) := by
      have hMask := bTruth_vecMask_r191 c s t (realCut_f realCoordinate_f) hVec
      have hs : c ≤ bTruth s (realCut_f realCoordinate_f) :=
        inf_le_right.trans (inf_le_left.trans inf_le_left)
      exact (le_inf le_rfl hs).trans (hMask.le.trans inf_le_right)
    have hImag : c ≤ bTruth t (realCut_f imagCoordinate_f) := by
      have hMask := bTruth_vecMask_r191 c s t (realCut_f imagCoordinate_f) hVec
      have hs : c ≤ bTruth s (realCut_f imagCoordinate_f) :=
        inf_le_right.trans (inf_le_left.trans inf_le_right)
      exact (le_inf le_rfl hs).trans (hMask.le.trans inf_le_right)
    have hCoords := forces_weightedComplex_coordinates v U W
    exact ⟨(forces_realCut_weighted_iff t realCoordinate_f U hCoords.1 c).1 hReal,
      (forces_realCut_weighted_iff t imagCoordinate_f W hCoords.2 c).1 hImag⟩
  constructor <;> rw [hCover] <;> apply properCutOn_iSup <;> intro x <;>
    apply properCutOn_iSup <;> intro y
  · exact (hCell x y).1
  · exact (hCell x y).2

end JSP000930.Positive
