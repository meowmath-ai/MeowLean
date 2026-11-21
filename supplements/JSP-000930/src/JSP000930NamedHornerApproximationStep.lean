import JSP000930GaussianRationalSeed

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem scalar_horner_step_bound (a b x y z : ℂ) {e E R : ℝ}
    (he : dist a b ≤ e) (hE : dist x y ≤ E) (hR : ‖z‖ ≤ R)
    (hE0 : 0 ≤ E) :
    dist (a + z*x) (b + z*y) ≤ e + R*E := by
  rw [dist_eq_norm,show (a + z*x) - (b + z*y) = (a-b) + z*(x-y) by ring]
  have h1 : ‖a-b‖ ≤ e := by simpa only [dist_eq_norm] using he
  have h2 : ‖x-y‖ ≤ E := by simpa only [dist_eq_norm] using hE
  apply (norm_add_le _ _).trans
  rw [Complex.norm_mul]
  exact add_le_add h1 (mul_le_mul hR h2 (norm_nonneg _) ((norm_nonneg z).trans hR))

theorem named_horner_step_bound (a b x y z : ComplexBits B) (m : B)
    (ha : a.CutOn m) (hb : b.CutOn m) (hx : x.CutOn m) (hy : y.CutOn m) (hz : z.CutOn m)
    (e E R : ℚ) (he : 0 ≤ e) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hAB : m ≤ distanceLe a b e) (hXY : m ≤ distanceLe x y E)
    (hZ : m ≤ distanceLe z (ComplexBits.checked (0 : ℂ)) R) :
    m ≤ distanceLe (a.add (z.mul x)) (b.add (z.mul y)) (e + R*E) := by
  let u : Fin 5 → ComplexBits B := ![a,b,x,y,z]
  have hu : ∀ i,(u i).CutOn m := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hx
    · exact hy
    · exact hz
  let α : Expr (Fin 5) := .add (.atom 0) (.mul (.atom 4) (.atom 2))
  let β : Expr (Fin 5) := .add (.atom 1) (.mul (.atom 4) (.atom 3))
  have hA : α.Safe u m := by intro t ht; exact (List.not_mem_nil ht).elim
  have hB : β.Safe u m := by intro t ht; exact (List.not_mem_nil ht).elim
  change m ≤ distanceLe (α.eval u) (β.eval u) (e + R*E)
  apply expr_distance_forced u m α β (e + R*E) hu hA hB (add_nonneg he (mul_nonneg hR hE))
  intro p w hp hnz hpm ht
  have h₁ := trace_distanceLe hp hnz hpm ha hb (ht 0) (ht 1) he hAB
  have h₂ := trace_distanceLe hp hnz hpm hx hy (ht 2) (ht 3) hE hXY
  have h3 := trace_distanceLe hp hnz hpm hz (ComplexBits.checked_cutOn 0 m)
    (ht 4) (checked_complex_traces p 0) hR hZ
  have h3' : ‖w 4‖ ≤ (R : ℝ) := by simpa only [dist_zero_right] using h3
  have h4 := scalar_horner_step_bound (w 0) (w 1) (w 2) (w 3) (w 4)
    h₁ h₂ h3' (by exact_mod_cast hE)
  simpa only [α,β,Expr.evalGround,Rat.cast_add,Rat.cast_mul] using h4

end JSP000930.Negative
