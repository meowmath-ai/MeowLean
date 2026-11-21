import JSP000930FiniteNormBounds

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem distanceLe_congr_right930 {m : B} {x y z : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) (hz : z.CutOn m)
    (hE : m ≤ y.name =ᴮ z.name) {e : ℚ} (he : 0 ≤ e)
    (hD : m ≤ distanceLe x y e) : m ≤ distanceLe x z e := by
  let u : Fin 3 → ComplexBits B := ![x,y,z]
  have hu : ∀ i,(u i).CutOn m := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  refine distanceLe_of_finite_metric_law u m hu 0 2 e ?_
  intro p w hp hnz hpm ht
  have h₀ : ComplexDecisionTrace p x (w 0) := ht 0
  have h₁ : ComplexDecisionTrace p y (w 1) := ht 1
  have h₂ : ComplexDecisionTrace p z (w 2) := ht 2
  have h1 := trace_distanceLe hp hnz hpm hx hy h₀ h₁ he hD
  have h2 := trace_complex_eq hp hnz hpm h₁ h₂ hE
  rw [← h2]
  exact pow_le_pow_left₀ dist_nonneg h1 2

end JSP000930.Negative
