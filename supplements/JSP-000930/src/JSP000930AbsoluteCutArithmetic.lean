import JSP000930AnalyticComplexBits
import JSP000933CompleteValueMap

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanCompletion JSP000933.BooleanNames

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem map_iSup_prop930 (F : CompleteValueMap B C) {P : Prop} (u : P → B) :
    F.toFun (⨆ h : P, u h) = ⨆ h : P, F.toFun (u h) := by
  by_cases h : P
  · simp only [iSup_pos h]
  · simp only [iSup_neg h, F.map_bot]

theorem map_iInf_prop930 (F : CompleteValueMap B C) {P : Prop} (u : P → B) :
    F.toFun (⨅ h : P, u h) = ⨅ h : P, F.toFun (u h) := by
  by_cases h : P
  · simp only [iInf_pos h]
  · simp only [iInf_neg h, F.map_top]

def mapCut (F : CompleteValueMap B C) (u : RatPresentation → B) :
    RatPresentation → C := fun q => F.toFun (u q)

theorem mapCut_checked (F : CompleteValueMap B C) (x : ℝ) :
    mapCut F (checkedRealBits x) = checkedRealBits x := by
  funext q
  by_cases h : (q.value : ℝ) < x
  · simp only [mapCut, checkedRealBits, JSP000933.PositiveForcing.crispTruth, ite_eq_left h, F.map_top]
  · simp only [mapCut, checkedRealBits, JSP000933.PositiveForcing.crispTruth, ite_eq_right h, F.map_bot]

theorem mapCut_add (F : CompleteValueMap B C) (u v : RatPresentation → B) :
    mapCut F (addCutBits u v) = addCutBits (mapCut F u) (mapCut F v) := by
  funext q
  simp only [mapCut, addCutBits, F.map_iSup, map_iSup_prop930 F, F.map_inf]

theorem mapCut_neg (F : CompleteValueMap B C) (u : RatPresentation → B) :
    mapCut F (negCutBits u) = negCutBits (mapCut F u) := by
  funext q
  simp only [mapCut, negCutBits, F.map_iSup, map_iSup_prop930 F, F.map_compl]

theorem mapCut_mul (F : CompleteValueMap B C) (u v : RatPresentation → B) :
    mapCut F (mulCutBits u v) = mulCutBits (mapCut F u) (mapCut F v) := by
  funext q
  simp only [mapCut, mulCutBits, intervalBits, F.map_iSup, map_iSup_prop930 F,
    F.map_inf, F.map_compl]

theorem mapCut_proper (F : CompleteValueMap B C) {p : B}
    {u : RatPresentation → B} (h : ProperCutOn p u) :
    ProperCutOn (F.toFun p) (mapCut F u) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mapCut, F.map_iSup] using F.monotone h.1
  · simpa only [mapCut, F.map_iSup, F.map_compl] using F.monotone h.2.1
  · intro q r hr
    simpa only [mapCut,F.map_inf] using F.monotone (h.2.2.1 q r hr)
  · intro q
    simpa only [mapCut,F.map_inf,F.map_iSup,map_iSup_prop930 F] using
      F.monotone (h.2.2.2 q)

def ComplexBits.map (F : CompleteValueMap B C) (x : ComplexBits B) : ComplexBits C :=
  ⟨mapCut F x.re, mapCut F x.im⟩

theorem ComplexBits.map_cutOn (F : CompleteValueMap B C) {p : B}
    {x : ComplexBits B} (hx : x.CutOn p) : (x.map F).CutOn (F.toFun p) :=
  ⟨mapCut_proper F hx.1, mapCut_proper F hx.2⟩

theorem ComplexBits.map_ofNat (F : CompleteValueMap B C) (n : ℕ) :
    (ComplexBits.ofNat (B := B) n).map F = ComplexBits.ofNat (B := C) n := by
  simp only [ComplexBits.ofNat, ComplexBits.map, mapCut_checked]

theorem ComplexBits.map_add (F : CompleteValueMap B C) (x y : ComplexBits B) :
    (x.add y).map F = (x.map F).add (y.map F) := by
  simp only [ComplexBits.add, ComplexBits.map, mapCut_add]

theorem ComplexBits.map_neg (F : CompleteValueMap B C) (x : ComplexBits B) :
    x.neg.map F = (x.map F).neg := by
  simp only [ComplexBits.neg, ComplexBits.map, mapCut_neg]

theorem ComplexBits.map_mul (F : CompleteValueMap B C) (x y : ComplexBits B) :
    (x.mul y).map F = (x.map F).mul (y.map F) := by
  simp only [ComplexBits.mul, ComplexBits.map, mapCut_add, mapCut_mul, mapCut_neg]

theorem ComplexBits.map_normSq (F : CompleteValueMap B C) (x : ComplexBits B) :
    mapCut F x.normSq = (x.map F).normSq := by
  simp only [ComplexBits.normSq, ComplexBits.map, mapCut_add, mapCut_mul]

theorem map_weightedCut_subset (F : CompleteValueMap B C)
    (u v : RatPresentation → B) :
    F.toFun (weightedRationalSet u ⊆ᴮ weightedRationalSet v) =
      (weightedRationalSet (mapCut F u) ⊆ᴮ weightedRationalSet (mapCut F v)) := by
  simp only [weightedRationalSet_subset, _root_.imp, F.map_iInf, F.map_sup_r93,
    F.map_compl, mapCut]

theorem ComplexBits.map_nameEq (F : CompleteValueMap B C) (x y : ComplexBits B) :
    F.toFun (x.name =ᴮ y.name) = ((x.map F).name =ᴮ (y.map F).name) := by
  rw [ComplexBits.name_eq, ComplexBits.name_eq]
  simp only [bSet.eq_iff_subset_subset, F.map_inf,
    map_weightedCut_subset, ComplexBits.map]

end JSP000930.BooleanAnalysis
