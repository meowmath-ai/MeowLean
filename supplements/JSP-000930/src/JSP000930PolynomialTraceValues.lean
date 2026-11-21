import JSP000930MixedPolynomialEvaluation

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.BooleanNames

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

abbrev RatGrid (R : ℕ) := {z : ℚ × ℚ // z.1 ^ 2 + z.2 ^ 2 ≤ (R : ℚ) ^ 2}

noncomputable def gridPoint {R : ℕ} (g : RatGrid R) : ℂ :=
  ⟨(g.1.1 : ℝ), (g.1.2 : ℝ)⟩

structure PolyTrace (B J : Type) where
  coeff : List (ComplexBits B)
  pins : Finset J
  radius : ℕ
  budget : ℚ
  budget_pos : 0 < budget

def PolyTrace.map (F : CompleteValueMap B C) (p : PolyTrace B J) : PolyTrace C J :=
  ⟨p.coeff.map (ComplexBits.map F), p.pins, p.radius, p.budget, p.budget_pos⟩

noncomputable def PolyTrace.eval (p : PolyTrace B J) (z : ComplexBits B) : ComplexBits B :=
  mixedPolynomialEval p.coeff z

theorem PolyTrace.eval_map (F : CompleteValueMap B C) (p : PolyTrace B J)
    (z : ComplexBits B) : (p.eval z).map F = (p.map F).eval (z.map F) :=
  map_mixedPolynomialEval F p.coeff z

noncomputable def distanceCut (x y : ComplexBits B) : RatPresentation → B :=
  (x.add y.neg).normSq

noncomputable def distanceLe (x y : ComplexBits B) (e : ℚ) : B :=
  weightedRationalSet (distanceCut x y) ⊆ᴮ
    weightedRationalSet (checkedRealBits ((e : ℝ) ^ 2))

theorem map_distanceLe (F : CompleteValueMap B C) (x y : ComplexBits B) (e : ℚ) :
    F.toFun (distanceLe x y e) = distanceLe (x.map F) (y.map F) e := by
  simp only [distanceLe, distanceCut, map_weightedCut_subset, ComplexBits.map_normSq,
    ComplexBits.map_add, ComplexBits.map_neg, mapCut_checked]

noncomputable def agreementValue (site : J → ComplexBits B) (q p : PolyTrace B J) : B :=
  ⨅ z : {z : J // z ∈ p.pins}, (q.eval (site z.1)).name =ᴮ (p.eval (site z.1)).name

noncomputable def discValue (q p : PolyTrace B J) : B :=
  ⨅ g : RatGrid p.radius, distanceLe
    (q.eval (ComplexBits.checked (gridPoint g))) (p.eval (ComplexBits.checked (gridPoint g)))
    (p.budget - q.budget)

noncomputable def refinesValue (site : J → ComplexBits B) (q p : PolyTrace B J) : B :=
  JSP000933.PositiveForcing.crispTruth B (p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧ p.radius ≤ q.radius) ⊓
    (agreementValue site q p ⊓ discValue q p)

noncomputable def paletteValue (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) : B :=
  ⨅ z : {z : J // z ∈ p.pins}, ⨆ n : ℕ, (p.eval (site z.1)).name =ᴮ (H z.1 n).name

theorem map_crisp_truth930 (F : CompleteValueMap B C) (P : Prop) :
    F.toFun (JSP000933.PositiveForcing.crispTruth B P) = JSP000933.PositiveForcing.crispTruth C P := by
  by_cases h : P
  · simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left h,F.map_top]
  · simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_right h,F.map_bot]

theorem map_agreementValue (F : CompleteValueMap B C) (site : J → ComplexBits B)
    (q p : PolyTrace B J) :
    F.toFun (agreementValue site q p) =
      agreementValue (fun z => (site z).map F) (q.map F) (p.map F) := by
  unfold agreementValue
  rw [F.map_iInf]
  apply iInf_congr
  intro z
  rw [ComplexBits.map_nameEq, q.eval_map, p.eval_map]

theorem map_discValue (F : CompleteValueMap B C) (q p : PolyTrace B J) :
    F.toFun (discValue q p) = discValue (q.map F) (p.map F) := by
  unfold discValue
  rw [F.map_iInf]
  apply iInf_congr
  intro g
  simp only [map_distanceLe, q.eval_map, p.eval_map, ComplexBits.map_checked, PolyTrace.map]

theorem map_refinesValue (F : CompleteValueMap B C) (site : J → ComplexBits B)
    (q p : PolyTrace B J) :
    F.toFun (refinesValue site q p) =
      refinesValue (fun z => (site z).map F) (q.map F) (p.map F) := by
  simp only [refinesValue, F.map_inf, map_crisp_truth930, map_agreementValue, map_discValue,
    PolyTrace.map]

theorem map_paletteValue (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) :
    F.toFun (paletteValue site H p) =
      paletteValue (fun z => (site z).map F) (fun z n => (H z n).map F) (p.map F) := by
  unfold paletteValue
  rw [F.map_iInf]
  apply iInf_congr
  intro z
  rw [F.map_iSup]
  apply iSup_congr
  intro n
  rw [ComplexBits.map_nameEq, p.eval_map]

end JSP000930.Negative
