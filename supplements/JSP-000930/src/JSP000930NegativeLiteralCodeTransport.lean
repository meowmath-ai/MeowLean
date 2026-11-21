import JSP000930NegativeNativeCodeTransport

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000933.SetLanguage
  JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def codeBitsOfComplexBits (a : ℕ → ComplexBits B) : JSP000930.Positive.TaylorSlot → B :=
  fun j => (a j.1).coord j.2.1 j.2.2

noncomputable def codeNameOfComplexBits (a : ℕ → ComplexBits B) : bSet B :=
  JSP000930.Positive.taylorCodeName (codeBitsOfComplexBits a)

theorem codeNameOfComplexBits_forces_entire {n : ℕ} (v : DVec (V B) n) (A : STerm n)
    (a : ℕ → ComplexBits B) (p : B) (he : bTerm v A = codeNameOfComplexBits a)
    (ha : ∀ n,(a n).CutOn p) (hg : GrowthOn p a) :
    p ≤ bTruth v (isEntireCode_f A) :=
  JSP000930.Positive.canonical_native_data_forces_entire v A (codeBitsOfComplexBits a) p he ha hg

theorem codeNameOfComplexBits_eval_iff {n : ℕ} (v : DVec (V B) n) (A Z Y : STerm n)
    (a : ℕ → ComplexBits B) (z : ComplexBits B) (p : B)
    (he : bTerm v A = codeNameOfComplexBits a) (hZ : bTerm v Z = z.name)
    (ha : ∀ n,(a n).CutOn p) (hg : GrowthOn p a) (hz : z.CutOn p) :
    p ≤ bTruth v (evalAt_f A Z Y) ↔ p ≤ bTerm v Y =ᴮ (taylorLimitBits a z).name := by
  have hE := codeNameOfComplexBits_forces_entire v A a p he ha hg
  have hS : p ≤ bTruth v (sequence_f A) := by
    simp only [isEntireCode_f,boolean_realize_bounded_formula_and] at hE
    exact hE.trans inf_le_left
  have hMask := JSP000930.Positive.canonical_sequence_bits_mask v A (codeBitsOfComplexBits a) p he hS
  have hEq : p ≤ (taylorLimitBits (sequenceBits (bTerm v A)) z).name =ᴮ (taylorLimitBits a z).name :=
    JSP000930.Positive.sameMaskedComplex_name
      (JSP000930.Positive.sameMaskedComplex_taylorLimit hMask (JSP000930.Positive.sameMaskedComplex_self p z))
  exact (forces_evalAt_iff_taylorLimit v A Z Y z p hZ hz hE).trans
    ⟨fun h => bSet.bv_trans h hEq,fun h => bSet.bv_trans h (hEq.trans_eq bSet.bv_eq_symm)⟩

noncomputable def transportedTaylorCode (F : CompleteValueMap B C) (a : ℕ → ComplexBits B) : bSet C :=
  codeNameOfComplexBits (fun i => (a i).map F)

theorem transportedTaylorCode_forces_entire (F : CompleteValueMap B C) {n : ℕ}
    (v : DVec (V C) n) (A : STerm n) (a : ℕ → ComplexBits B) (p : B)
    (hA : bTerm v A = transportedTaylorCode F a)
    (ha : ∀ i,(a i).CutOn p) (hg : GrowthOn p a) :
    F.toFun p ≤ bTruth v (isEntireCode_f A) :=
  codeNameOfComplexBits_forces_entire v A _ (F.toFun p) hA
    (fun i => ComplexBits.map_cutOn F (ha i)) (hg.map F)

theorem transportedTaylorCode_eval_iff (F : CompleteValueMap B C) {n : ℕ}
    (v : DVec (V C) n) (A Z Y : STerm n)
    (a : ℕ → ComplexBits B) (z : ComplexBits B) (p : B)
    (hA : bTerm v A = transportedTaylorCode F a) (hZ : bTerm v Z = (z.map F).name)
    (ha : ∀ i,(a i).CutOn p) (hg : GrowthOn p a) (hz : z.CutOn p) :
    F.toFun p ≤ bTruth v (evalAt_f A Z Y) ↔
      F.toFun p ≤ bTerm v Y =ᴮ ((taylorLimitBits a z).map F).name := by
  rw [map_taylorLimitBits]
  exact codeNameOfComplexBits_eval_iff v A Z Y (fun i => (a i).map F) (z.map F) (F.toFun p) hA hZ
    (fun i => ComplexBits.map_cutOn F (ha i)) (hg.map F) (ComplexBits.map_cutOn F hz)

theorem transportedActualFineTower_pin_literal_eval
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (G : CompleteValueMap (TotalBA (polynomialQ site H)) C)
    (pin : PolyTrace B J) (j : J) (hj : j ∈ pin.pins) (hSite : (site j).CutOn (⊤ : B))
    {n : ℕ} (v : DVec (V C) n) (A Z Y : STerm n)
    (hA : bTerm v A = transportedTaylorCode G (actualFinePolynomialTower site H).limitCoefficients)
    (hZ : bTerm v Z = (((site j).map (polynomialBaseValueMap site H)).map G).name) :
    let F := polynomialBaseValueMap site H
    let m := traceValue (polynomialQ site H) (some pin)
    G.toFun m ≤ bTruth v (evalAt_f A Z Y) ↔
      G.toFun m ≤ bTerm v Y =ᴮ (((pin.eval (site j)).map F).map G).name := by
  let T := actualFinePolynomialTower site H
  let F := polynomialBaseValueMap site H
  let z := (site j).map F
  let y := (pin.eval (site j)).map F
  let m := traceValue (polynomialQ site H) (some pin)
  have hT : T.On m := (actualFinePolynomialTower_on site H).mono le_top
  have hz : z.CutOn m := by
    apply complexCutOn_mono (show m ≤ (⊤ : TotalBA (polynomialQ site H)) from le_top)
    simpa only [z,F.map_top] using ComplexBits.map_cutOn F hSite
  have h := transportedTaylorCode_eval_iff G v A Z Y T.limitCoefficients z m hA hZ
    (T.limit_coeff_proper m hT) (T.limitGrowth m hT) hz
  have he : G.toFun m ≤ ((taylorLimitBits T.limitCoefficients z).map G).name =ᴮ (y.map G).name := by
    have hPin := actualFineTower_preserves_pin site H pin j hj hSite
    have hm := G.monotone hPin
    simpa only [ComplexBits.map_nameEq] using hm
  exact h.trans ⟨fun h => bSet.bv_trans h he,fun h => bSet.bv_trans h (he.trans_eq bSet.bv_eq_symm)⟩

end JSP000930.Negative
