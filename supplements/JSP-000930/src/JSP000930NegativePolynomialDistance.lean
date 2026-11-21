import JSP000930NegativePolynomialMix

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem distanceLe_congr_of_named_eq {m : B} {u v x y : ComplexBits B} {e : ℚ}
    (hu : u.CutOn m) (hv : v.CutOn m) (hx : x.CutOn m) (hy : y.CutOn m)
    (he : 0 ≤ e) (hU : m ≤ u.name =ᴮ x.name) (hV : m ≤ v.name =ᴮ y.name)
    (h : m ≤ distanceLe x y e) : m ≤ distanceLe u v e := by
  let F : Fin 4 → ComplexBits B := ![u,v,x,y]
  have hf : ∀ i,(F i).CutOn m := by
    intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hx
    · exact hy
  refine distanceLe_of_finite_metric_law F m hf 0 1 e ?_
  intro p w hp hn hpm ht
  have hU' : w 0 = w 2 := trace_complex_eq hp hn hpm (ht 0) (ht 2) hU
  have hV' : w 1 = w 3 := trace_complex_eq hp hn hpm (ht 1) (ht 3) hV
  have hD := trace_distanceLe hp hn hpm hx hy (ht 2) (ht 3) he h
  rw [hU',hV']
  exact pow_le_pow_left₀ dist_nonneg hD 2

private theorem coordinate_abs_le_norm_sub (x y : ℂ) (b : Bool) :
    |complexCoord x b-complexCoord y b| ≤ dist x y := by
  cases b
  · simpa [complexCoord,dist_eq_norm,Complex.sub_re] using Complex.abs_re_le_norm (x-y)
  · simpa [complexCoord,dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (x-y)

theorem coordNear_of_named_distanceLe {m : B} {u v : ComplexBits B} {e ε : ℚ}
    (hu : u.CutOn m) (hv : v.CutOn m) (he : 0 ≤ e) (he' : e < ε)
    (h : m ≤ distanceLe u v e) (b : Bool) :
    m ≤ cutNear (u.coord b) (v.coord b) ε := by
  have H (rev : Bool) :
      m ≤ if rev then directedNear (v.coord b) (u.coord b) ε else
        directedNear (u.coord b) (v.coord b) ε := by
    by_contra hb
    let U := if rev then v else u
    let V := if rev then u else v
    have hb' : ¬ m ≤ directedNear (U.coord b) (V.coord b) ε := by cases rev <;> exact hb
    obtain ⟨q,r,s,hs,hsm,hqr,hlo,hhi⟩ := directedNear_countercell hb'
    have hu' := JSP000930.AnalyticSyntax.complexCutOn_mono hsm hu
    have hv' := JSP000930.AnalyticSyntax.complexCutOn_mono hsm hv
    obtain ⟨p,x,y,hp,hn,hps,htx,hty⟩ := twoComplex_decisionCompletion u v s hs hu' hv'
    have hD := trace_distanceLe hp hn hps hu' hv' htx hty he (hsm.trans h)
    have hE : (e : ℝ) < (ε : ℝ) := by exact_mod_cast he'
    cases rev
    · have hGap := trace_directedNear_failure_forces_gap hp hn (htx.coordinate b) (hty.coordinate b)
        q r hqr ⟨0,(hps 0).trans hlo⟩ ⟨0,(hps 0).trans hhi⟩
      exact (not_le_of_gt hE)
        (hGap.trans ((le_abs_self _).trans ((coordinate_abs_le_norm_sub x y b).trans hD)))
    · have hGap := trace_directedNear_failure_forces_gap hp hn (hty.coordinate b) (htx.coordinate b)
        q r hqr ⟨0,(hps 0).trans hlo⟩ ⟨0,(hps 0).trans hhi⟩
      have hRev : dist y x ≤ (e : ℝ) := by rwa [dist_comm y x]
      exact (not_le_of_gt hE)
        (hGap.trans ((le_abs_self _).trans ((coordinate_abs_le_norm_sub y x b).trans hRev)))
  exact le_inf (H false) (H true)

end JSP000930.Negative
