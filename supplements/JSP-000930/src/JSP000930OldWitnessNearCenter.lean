import JSP000930OldDenseSetActualCenter
import JSP000930NegativePolynomialNamedGrid

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem old_witness_eval_near_center (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (q p : PolyTrace B J)
    (m : B) (hm : m ≠ ⊥)
    (h : m ≤ (polynomialQ site H).refines (some q) (some p))
    (z : ComplexBits B) (hz : z.CutOn m) (c : ℂ)
    (hEq : m ≤ (p.eval z).name =ᴮ (ComplexBits.checked c).name)
    (K : ℕ) (hK : m ≤ halfRadiusBound z K) (hR : (K : ℝ)/2 < (p.radius : ℝ)) :
    m ≤ distanceLe (q.eval z) (ComplexBits.checked c) p.budget := by
  have hVq : m ≤ coeffValue q.coeff := h.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hVp : m ≤ coeffValue p.coeff := h.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))
  have hr : m ≤ refinesValue site q p := h.trans inf_le_right
  obtain ⟨_,hB,_⟩ := structural_of_weighted_refines site q p m hm hr
  have hBd := sub_nonneg.mpr hB
  have hDisc : m ≤ discValue q p := hr.trans (inf_le_right.trans inf_le_right)
  have hd : m ≤ distanceLe (q.eval z) (p.eval z) (p.budget-q.budget) :=
    grid_distanceLe_at_named_point q.coeff p.coeff z m
      ((le_coeffValue_iff _ _).mp hVq) ((le_coeffValue_iff _ _).mp hVp) hz K p.radius
      hK hR _ hBd (fun g => hDisc.trans (iInf_le _ g))
  have hq := eval_cutOn_of_coeff hVq hz
  have hp := eval_cutOn_of_coeff hVp hz
  have hC := ComplexBits.checked_cutOn c m
  have h := distanceLe_congr_right930 hq hp hC hEq hBd hd
  exact distanceLe_mono hq hC hBd (sub_le_self _ q.budget_pos.le) h

end JSP000930.Negative
