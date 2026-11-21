import JSP000930AnalyticComplexBinders

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure ComplexBits (B : Type) where
  re : RatPresentation → B
  im : RatPresentation → B

def ComplexBits.CutOn (z : ComplexBits B) (p : B) : Prop :=
  ProperCutOn p z.re ∧ ProperCutOn p z.im

def ComplexBits.name (z : ComplexBits B) : bSet B :=
  bSet.pair (weightedRationalSet z.re) (weightedRationalSet z.im)

noncomputable def ComplexBits.ofNat (n : ℕ) : ComplexBits B :=
  ⟨checkedRealBits n,checkedRealBits 0⟩

noncomputable def ComplexBits.neg (z : ComplexBits B) : ComplexBits B :=
  ⟨negCutBits z.re,negCutBits z.im⟩

noncomputable def ComplexBits.add (x y : ComplexBits B) : ComplexBits B :=
  ⟨addCutBits x.re y.re,addCutBits x.im y.im⟩

noncomputable def ComplexBits.mul (x y : ComplexBits B) : ComplexBits B :=
  ⟨addCutBits (mulCutBits x.re y.re) (negCutBits (mulCutBits x.im y.im)),
   addCutBits (mulCutBits x.re y.im) (mulCutBits x.im y.re)⟩

noncomputable def ComplexBits.normSq (z : ComplexBits B) : RatPresentation → B :=
  addCutBits (mulCutBits z.re z.re) (mulCutBits z.im z.im)

theorem ComplexBits.ofNat_cutOn (n : ℕ) (p : B) :
    (ComplexBits.ofNat (B := B) n).CutOn p :=
  ⟨properCutOn_mono le_top (checkedRealBits_properCut (n : ℝ)),
    properCutOn_mono le_top (checkedRealBits_properCut 0)⟩

theorem ComplexBits.neg_cutOn {z : ComplexBits B} {p : B} (h : z.CutOn p) :
    z.neg.CutOn p :=
  ⟨negCutBits_properCut _ p h.1,negCutBits_properCut _ p h.2⟩

theorem ComplexBits.add_cutOn {x y : ComplexBits B} {p : B}
    (hx : x.CutOn p) (hy : y.CutOn p) : (x.add y).CutOn p :=
  ⟨addCutBits_properCut _ _ p hx.1 hy.1,addCutBits_properCut _ _ p hx.2 hy.2⟩

theorem ComplexBits.mul_cutOn {x y : ComplexBits B} {p : B}
    (hx : x.CutOn p) (hy : y.CutOn p) : (x.mul y).CutOn p :=
  ⟨addCutBits_properCut _ _ p (mulCutBits_properCut _ _ p hx.1 hy.1)
       (negCutBits_properCut _ p (mulCutBits_properCut _ _ p hx.2 hy.2)),
    addCutBits_properCut _ _ p (mulCutBits_properCut _ _ p hx.1 hy.2)
       (mulCutBits_properCut _ _ p hx.2 hy.1)⟩

theorem ComplexBits.normSq_cutOn {z : ComplexBits B} {p : B} (h : z.CutOn p) :
    ProperCutOn p z.normSq :=
  addCutBits_properCut _ _ p (mulCutBits_properCut _ _ p h.1 h.1)
    (mulCutBits_properCut _ _ p h.2 h.2)

theorem ComplexBits.name_eq (x y : ComplexBits B) :
    (x.name =ᴮ y.name) =
      (weightedRationalSet x.re =ᴮ weightedRationalSet y.re) ⊓
      (weightedRationalSet x.im =ᴮ weightedRationalSet y.im) := by
  simp only [ComplexBits.name,JSP000933.PositiveForcing.pair_eq_inf_r189]

end JSP000930.BooleanAnalysis
