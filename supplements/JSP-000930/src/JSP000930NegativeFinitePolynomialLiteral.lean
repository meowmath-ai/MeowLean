import JSP000930NegativeFinitePolynomialEvaluation
import JSP000930PositiveCanonicalNativeGrowthForcesLiteralEntire

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000930.Positive
  JSP000933.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def polynomialCodeBits (f : List (ComplexBits B)) : TaylorSlot → B :=
  fun j => (zeroPaddedPoly f j.1).coord j.2.1 j.2.2

noncomputable def polynomialCodeName (f : List (ComplexBits B)) : bSet B :=
  taylorCodeName (polynomialCodeBits f)

private theorem polyCode_coeff (f : List (ComplexBits B)) (i : ℕ) :
    complexCoeffBits (polynomialCodeBits f) i = zeroPaddedPoly f i := by
  rfl

theorem polynomialCode_forces_entire {n : ℕ} (v : DVec (V B) n) (A : STerm n)
    (f : List (ComplexBits B)) (p : B) (hA : bTerm v A = polynomialCodeName f)
    (hf : ∀ c ∈ f,c.CutOn p) :
    p ≤ bTruth v (isEntireCode_f A) := by
  refine canonical_native_data_forces_entire v A (polynomialCodeBits f) p hA
    (fun i => ?_) ?_
  · rw [polyCode_coeff]
    exact zeroPaddedPoly_cutOn f p hf i
  · have h : complexCoeffBits (polynomialCodeBits f) = zeroPaddedPoly f :=
      funext (polyCode_coeff f)
    rw [h]
    exact zeroPaddedPoly_growth f p hf

theorem polynomialCode_eval_iff_horner {n : ℕ} (v : DVec (V B) n)
    (A Z Y : STerm n) (f : List (ComplexBits B)) (z : ComplexBits B) (p : B)
    (hA : bTerm v A = polynomialCodeName f) (hZ : bTerm v Z = z.name)
    (hf : ∀ c ∈ f,c.CutOn p) (hz : z.CutOn p) :
    p ≤ bTruth v (evalAt_f A Z Y) ↔ p ≤ bTerm v Y =ᴮ (mixedPolynomialEval f z).name := by
  have hEntire := polynomialCode_forces_entire v A f p hA hf
  have hSeq : p ≤ bTruth v (sequence_f A) := by
    simp only [isEntireCode_f,boolean_realize_bounded_formula_and] at hEntire
    exact hEntire.trans inf_le_left
  have hMask := canonical_sequence_bits_mask v A (polynomialCodeBits f) p hA hSeq
  have hMask' (i : ℕ) : sameMaskedComplex p (sequenceBits (bTerm v A) i) (zeroPaddedPoly f i) := by
    rw [← polyCode_coeff f i]
    exact hMask i
  have hm := sameMaskedComplex_name (sameMaskedComplex_taylorLimit hMask' (sameMaskedComplex_self p z))
  have he := bSet.bv_trans hm (zeroPaddedPoly_limit_eq_horner f z p hf hz)
  exact (forces_evalAt_iff_taylorLimit v A Z Y z p hZ hz hEntire).trans
    ⟨fun h => bSet.bv_trans h he,fun h => bSet.bv_trans h (he.trans_eq bSet.bv_eq_symm)⟩

end JSP000930.Negative
