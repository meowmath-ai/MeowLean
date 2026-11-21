import JSP000930AbsoluteCutArithmetic
import JSP000930AnalyticComplexTrace

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanCompletion

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def ComplexBits.checked (z : ℂ) : ComplexBits B :=
  ⟨checkedRealBits z.re, checkedRealBits z.im⟩

theorem ComplexBits.checked_cutOn (z : ℂ) (p : B) : (ComplexBits.checked z).CutOn p :=
  ⟨properCutOn_mono le_top (checkedRealBits_properCut z.re),
    properCutOn_mono le_top (checkedRealBits_properCut z.im)⟩

theorem ComplexBits.map_checked (F : CompleteValueMap B C) (z : ℂ) :
    (ComplexBits.checked z).map F = ComplexBits.checked z := by
  simp only [ComplexBits.checked, ComplexBits.map, mapCut_checked]

noncomputable def mixedPolynomialEval (a : List (ComplexBits B)) (z : ComplexBits B) :
    ComplexBits B :=
  a.foldr (fun c t => c.add (z.mul t)) (ComplexBits.ofNat 0)

def scalarPolynomialEval (a : List ℂ) (z : ℂ) : ℂ :=
  a.foldr (fun c t => c + z * t) 0

theorem mixedPolynomialEval_cutOn (a : List (ComplexBits B)) (z : ComplexBits B)
    {p : B} (ha : ∀ c ∈ a, c.CutOn p) (hz : z.CutOn p) :
    (mixedPolynomialEval a z).CutOn p := by
  induction a with
  | nil => exact ComplexBits.ofNat_cutOn 0 p
  | cons c u ih =>
    change (c.add (z.mul (mixedPolynomialEval u z))).CutOn p
    have hc := ha c List.mem_cons_self
    exact ComplexBits.add_cutOn hc
      (ComplexBits.mul_cutOn hz (ih (fun d hd => ha d (List.mem_cons_of_mem _ hd))))

theorem map_mixedPolynomialEval (F : CompleteValueMap B C)
    (a : List (ComplexBits B)) (z : ComplexBits B) :
    (mixedPolynomialEval a z).map F =
      mixedPolynomialEval (a.map (ComplexBits.map F)) (z.map F) := by
  induction a with
  | nil => exact ComplexBits.map_ofNat F 0
  | cons c u ih =>
    change (c.add (z.mul (mixedPolynomialEval u z))).map F =
      (c.map F).add ((z.map F).mul (mixedPolynomialEval (u.map (ComplexBits.map F)) (z.map F)))
    rw [ComplexBits.map_add, ComplexBits.map_mul, ih]

theorem checked_complex_traces (p : ℕ → B) (z : ℂ) :
    ComplexDecisionTrace p (ComplexBits.checked z) z :=
  ⟨checkedRealBits_traces p z.re, checkedRealBits_traces p z.im⟩

theorem trace_mixedPolynomialEval {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m)
    {z : ComplexBits B} {w : ℂ} (hz : z.CutOn m)
    (htz : ComplexDecisionTrace p z w)
    (a : List (ComplexBits B × ℂ))
    (ha : ∀ c ∈ a, c.1.CutOn m ∧ ComplexDecisionTrace p c.1 c.2) :
    ComplexDecisionTrace p (mixedPolynomialEval (a.map Prod.fst) z)
      (scalarPolynomialEval (a.map Prod.snd) w) := by
  induction a with
  | nil => exact ComplexDecisionTrace.ofNat p 0
  | cons c u ih =>
    change ComplexDecisionTrace p
      (c.1.add (z.mul (mixedPolynomialEval (u.map Prod.fst) z)))
      (c.2 + w * scalarPolynomialEval (u.map Prod.snd) w)
    have hc := ha c List.mem_cons_self
    have hu : ∀ d ∈ u, d.1.CutOn m ∧ ComplexDecisionTrace p d.1 d.2 :=
      fun d hd => ha d (List.mem_cons_of_mem _ hd)
    have hTail : (mixedPolynomialEval (u.map Prod.fst) z).CutOn m := by
      apply mixedPolynomialEval_cutOn _ z _ hz
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (hu e he).1
    have ht := ih hu
    have hProd := htz.mul hp hpm ht hz hTail
    exact hc.2.add hp hpm hProd hc.1 (ComplexBits.mul_cutOn hz hTail)

end JSP000930.BooleanAnalysis
