import JSP000930NamedPositiveSquaredNorm
import JSP000933FiniteBooleanWitnesses

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Negative JSP000933.BooleanNames JSP000933.CantorCodes
  JSP000933.BooleanCompletion

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def ComplexBits.inv (x : ComplexBits B) : ComplexBits B :=
  ⟨mulCutBits x.re (reciprocalCutBits x.normSq),
    mulCutBits (negCutBits x.im) (reciprocalCutBits x.normSq)⟩

theorem ComplexBits.map_inv (F : CompleteValueMap B C) (x : ComplexBits B) :
    x.inv.map F = (x.map F).inv := by
  simp only [ComplexBits.inv, ComplexBits.map, mapCut_mul, mapCut_neg,
    map_reciprocalCutBits, ComplexBits.map_normSq]

theorem ComplexBits.inv_cutOn {m : B} {x : ComplexBits B} (hx : x.CutOn m)
    (hpos : m ≤ positiveCutValue x.normSq) : x.inv.CutOn m := by
  have hRec := reciprocalCut_proper (ComplexBits.normSq_cutOn hx) hpos
  exact ⟨mulCutBits_properCut _ _ m hx.1 hRec,
    mulCutBits_properCut _ _ m (negCutBits_properCut _ m hx.2) hRec⟩

theorem ComplexDecisionTrace.inv_of_positive {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u : ComplexBits B} {x : ℂ}
    (hU : u.CutOn m) (hu : ComplexDecisionTrace p u x)
    (hpos : m ≤ positiveCutValue u.normSq) (hx : 0 < Complex.normSq x) :
    ComplexDecisionTrace p u.inv x⁻¹ := by
  have hRec := reciprocalCut_proper (ComplexBits.normSq_cutOn hU) hpos
  have hr := trace_reciprocalCut hpm (ComplexBits.normSq_cutOn hU)
    (hu.normSq hp hpm hU) hx
  constructor
  · simpa only [ComplexBits.inv, Complex.inv_re, div_eq_mul_inv, one_div, one_mul] using
      hu.1.mul hp hpm hr hU.1 hRec
  · simpa only [ComplexBits.inv, Complex.inv_im, div_eq_mul_inv, one_div, one_mul,
      neg_mul] using (hu.2.neg hpm hU.2).mul hp hpm hr
        (negCutBits_properCut _ m hU.2) hRec

theorem ComplexBits.mul_inv_forced {m : B} {u : ComplexBits B} (hu : u.CutOn m)
    (hpos : m ≤ positiveCutValue u.normSq) :
    m ≤ (u.mul u.inv).name =ᴮ (ComplexBits.checked (B := B) 1).name := by
  by_contra hFail
  have hInv := ComplexBits.inv_cutOn hu hpos
  have hProd := ComplexBits.mul_cutOn hu hInv
  obtain ⟨s,hs,hsM,hSep⟩ := complex_eq_fail_survives hProd
    (ComplexBits.checked_cutOn 1 m) hFail
  obtain ⟨q,r,hr,hrs,hrQ⟩ := exists_nonzero_below_choice_r135 s hs
    (fun q : {q : RatPresentation // 0 < q.value} => u.normSq q.1)
    (hsM.trans hpos)
  have hRM := hrs.trans hsM
  have hUr : u.CutOn r := ⟨properCutOn_mono hRM hu.1,properCutOn_mono hRM hu.2⟩
  obtain ⟨p,x,hp,hnz,hpr,hxt⟩ :=
    exists_complex_decision_completion (fun _ : Unit => u) r hr (fun _ => hUr)
  have hpm : ∀ n, p n ≤ m := fun n => (hpr n).trans hRM
  have hps : ∀ n, p n ≤ s := fun n => (hpr n).trans hrs
  have hxTr : ComplexDecisionTrace p u (x ()) := hxt ()
  have hSQ := trace_forcedMember_le hp hnz (hxTr.normSq hp hpm hu) q.1
    ⟨0,(hpr 0).trans hrQ⟩
  have hQ : (0 : ℝ) < (q.1.value : ℝ) := by exact_mod_cast q.2
  have hX : 0 < Complex.normSq (x ()) := hQ.trans_le hSQ
  have hxInv := ComplexDecisionTrace.inv_of_positive hp hpm hu hxTr hpos hX
  have hFinal := hxTr.mul hp hpm hxInv hu hInv
  exact hSep hp hnz hps hFinal (checked_complex_traces p 1)
    (mul_inv_cancel₀ (Complex.normSq_pos.mp hX))

end JSP000930.BooleanAnalysis
