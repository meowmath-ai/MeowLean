import JSP000930GenericPinnedTraceBound
import JSP000930NegativePolynomialNamedGrid

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem activeTrace_pin_bound_at_radius
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a p : PolyTrace B J) (z : J) (hz : z ∈ p.pins) (hSite : (site z).CutOn (⊤ : B))
    (K : ℕ) (hR : (K : ℝ) / 2 < (a.radius : ℝ)) :
    (traceValue (polynomialQ site H) (some a) ⊓ traceValue (polynomialQ site H) (some p)) ⊓
        baseEmbed (polynomialQ site H) (halfRadiusBound (site z) K) ≤
      baseEmbed (polynomialQ site H) (distanceLe (a.eval (site z)) (p.eval (site z)) a.budget) := by
  apply activeTrace_pin_bound site H a p z hz hSite
  intro q m hm hQ hA hD hBudget
  exact grid_distanceLe_at_named_point q.coeff a.coeff (site z) m
    ((le_coeffValue_iff _ _).mp hQ) ((le_coeffValue_iff _ _).mp hA)
    (cutOn_mono930 hSite le_top) K a.radius hm hR (a.budget - q.budget)
    (sub_nonneg.mpr hBudget) (fun g => hD.trans (iInf_le _ g))

end JSP000930.Negative
