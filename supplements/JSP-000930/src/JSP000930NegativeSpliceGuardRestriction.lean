import JSP000930NegativeNamedSpliceCommonRefinement

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def NamedSpliceGuard.mono {site : J → ComplexBits B} {z : J} {old : List J} {R : ℕ}
    {m s : B} (G : NamedSpliceGuard site z old R m) (h : s ≤ m) :
    NamedSpliceGuard site z old R s :=
  ⟨G.coeff,G.bound,G.bound_one,fun c hc => cutOn_mono930 (G.coeff_cut c hc) h,
    h.trans G.at_new,fun i hi => h.trans (G.at_old i hi),fun g => h.trans (G.grid_bound g)⟩

theorem namedSplice_quarter_budget (E L e d : ℚ) (hE : 0 < E) (hL : 1 ≤ L)
    (he : e ≤ E/(4*L)) (hd : d ≤ E/4) :
    L*e+d ≤ E-E/2 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hD : 4*L ≠ 0 := mul_ne_zero (by norm_num) hL0.ne'
  have hEq : L * (E/(4*L)) = E/4 := by
    field_simp
  have hM : L*e ≤ E/4 :=
    (mul_le_mul_of_nonneg_left he hL0.le).trans_eq hEq
  linarith

end JSP000930.Negative
