import JSP000930NegativeNamedSpliceCoefficients

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem spliceValue_cutOn {a h g : ComplexBits B} {m : B}
    (ha : a.CutOn m) (hh : h.CutOn m) (hg : g.CutOn m) :
    (spliceValue a h g).CutOn m :=
  ComplexBits.add_cutOn ha (ComplexBits.mul_cutOn hg (ComplexBits.add_cutOn hh (ComplexBits.neg_cutOn ha)))

private abbrev SpliceAtom := Bool ⊕ Unit

private def spliceValueEnv (a h g : ComplexBits B) : SpliceAtom → ComplexBits B
  | .inl false => a
  | .inl true => h
  | .inr _ => g

private def leftAtom : SpliceAtom := .inl false
private def midAtom : SpliceAtom := .inl true
private def guardAtom : SpliceAtom := .inr ()

private def spliceValueExpr : Expr SpliceAtom :=
  .add (.atom leftAtom) (.mul (.atom guardAtom) (.add (.atom midAtom) (.neg (.atom leftAtom))))

private theorem spliceValueExpr_safe (u : SpliceAtom → ComplexBits B) (m : B) :
    spliceValueExpr.Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

private theorem spliceEnv_cut (a h g : ComplexBits B) (m : B)
    (ha : a.CutOn m) (hh : h.CutOn m) (hg : g.CutOn m) :
    ∀ i,(spliceValueEnv a h g i).CutOn m := by
  rintro (i | i)
  · cases i
    · exact ha
    · exact hh
  · exact hg

theorem spliceValue_eq_on {a h g : ComplexBits B} {m : B}
    (ha : a.CutOn m) (hh : h.CutOn m) (hg : g.CutOn m) (mid : Bool)
    (hTest : if mid then m ≤ g.name =ᴮ (ComplexBits.checked (1 : ℂ)).name
      else (m ≤ g.name =ᴮ (ComplexBits.checked (0 : ℂ)).name) ∨ (m ≤ h.name =ᴮ a.name)) :
    m ≤ (spliceValue a h g).name =ᴮ (if mid then h else a).name := by
  let u := spliceValueEnv a h g
  let o : SpliceAtom := if mid then midAtom else leftAtom
  have hU := spliceEnv_cut a h g m ha hh hg
  have ho : (Expr.atom o).Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hEq := expr_eq_forced u m spliceValueExpr (.atom o) hU (spliceValueExpr_safe u m) ho (by
    intro p w ht hn hpm hTr
    change w leftAtom + w guardAtom * (w midAtom + -w leftAtom) = w o
    rcases mid with _|_
    · rcases hTest with h0|hSame
      · have hg0 : w guardAtom = 0 :=
          trace_complex_eq ht hn hpm (hTr guardAtom) (checked_complex_traces p 0) h0
        change _ = w leftAtom
        rw [hg0,zero_mul,add_zero]
      · have hS : w midAtom = w leftAtom :=
          trace_complex_eq ht hn hpm (hTr midAtom) (hTr leftAtom) hSame
        change _ = w leftAtom
        rw [hS,add_neg_cancel,mul_zero,add_zero]
    · have h1 : w guardAtom = 1 :=
        trace_complex_eq ht hn hpm (hTr guardAtom) (checked_complex_traces p 1) hTest
      change _ = w midAtom
      rw [h1,one_mul]
      abel)
  cases mid <;> exact hEq

theorem spliceValue_distance_left {a h g : ComplexBits B} {m : B}
    (ha : a.CutOn m) (hh : h.CutOn m) (hg : g.CutOn m) (L e : ℚ)
    (hL : 0 ≤ L) (he : 0 ≤ e)
    (hG : m ≤ distanceLe g (ComplexBits.checked (0 : ℂ)) L)
    (hH : m ≤ distanceLe h a e) :
    m ≤ distanceLe (spliceValue a h g) a (L*e) := by
  let u := spliceValueEnv a h g
  have hU := spliceEnv_cut a h g m ha hh hg
  have ho : (Expr.atom leftAtom).Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hn := expr_distance_forced_with_aux u m spliceValueExpr (.atom leftAtom) [] (L*e)
    hU (spliceValueExpr_safe u m) ho (by intro x hx; exact (List.not_mem_nil hx).elim) (by
      intro p w hp hNZ hpm hTr _
      have hg' : ‖w guardAtom‖ ≤ (L : ℝ) := by
        simpa only [dist_zero_right] using
          trace_distanceLe hp hNZ hpm hg (ComplexBits.checked_cutOn 0 m)
            (hTr guardAtom) (checked_complex_traces p 0) hL hG
      have hh' : ‖w midAtom - w leftAtom‖ ≤ (e : ℝ) := by
        simpa only [dist_eq_norm] using
          trace_distanceLe hp hNZ hpm hh ha (hTr midAtom) (hTr leftAtom) he hH
      change dist (w leftAtom + w guardAtom * (w midAtom + -w leftAtom)) (w leftAtom) ≤ ((L*e : ℚ) : ℝ)
      rw [dist_eq_norm,← sub_eq_add_neg]
      have hEq : w leftAtom + w guardAtom * (w midAtom - w leftAtom) - w leftAtom =
          w guardAtom * (w midAtom - w leftAtom) := by ring
      rw [hEq,Complex.norm_mul,Rat.cast_mul]
      exact mul_le_mul hg' hh' (norm_nonneg _) (by exact_mod_cast hL))
  exact hn

end JSP000930.Negative
