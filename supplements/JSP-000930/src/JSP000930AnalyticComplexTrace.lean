import JSP000930AnalyticDecisionTraceMul
import JSP000930AnalyticTaylor

open Lattice
open scoped Flypitch bSet BigOperators

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def ComplexDecisionTrace (p : ℕ → B) (u : ComplexBits B) (z : ℂ) : Prop :=
  CutDecisionTrace p u.re z.re ∧ CutDecisionTrace p u.im z.im

theorem ComplexDecisionTrace.ofNat (p : ℕ → B) (n : ℕ) :
    ComplexDecisionTrace p (ComplexBits.ofNat n) (n : ℂ) := by
  exact ⟨by simpa [ComplexBits.ofNat] using checkedRealBits_traces p (n : ℝ),
    by simpa [ComplexBits.ofNat] using checkedRealBits_traces p 0⟩

theorem ComplexDecisionTrace.add {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : ComplexBits B} {x y : ℂ}
    (hu : ComplexDecisionTrace p u x) (hv : ComplexDecisionTrace p v y)
    (hU : u.CutOn m) (hV : v.CutOn m) :
    ComplexDecisionTrace p (u.add v) (x+y) := by
  refine ⟨?_,?_⟩
  · simpa [ComplexBits.add,Complex.add_re] using hu.1.add hp hpm hv.1 hU.1 hV.1
  · simpa [ComplexBits.add,Complex.add_im] using hu.2.add hp hpm hv.2 hU.2 hV.2

theorem ComplexDecisionTrace.neg {p : ℕ → B} {m : B} (hpm : ∀ n, p n ≤ m)
    {u : ComplexBits B} {x : ℂ} (hu : ComplexDecisionTrace p u x) (hU : u.CutOn m) :
    ComplexDecisionTrace p u.neg (-x) := by
  exact ⟨by simpa [ComplexBits.neg,Complex.neg_re] using hu.1.neg hpm hU.1,
    by simpa [ComplexBits.neg,Complex.neg_im] using hu.2.neg hpm hU.2⟩

theorem ComplexDecisionTrace.mul {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : ComplexBits B} {x y : ℂ}
    (hu : ComplexDecisionTrace p u x) (hv : ComplexDecisionTrace p v y)
    (hU : u.CutOn m) (hV : v.CutOn m) :
    ComplexDecisionTrace p (u.mul v) (x*y) := by
  have hrr := hu.1.mul hp hpm hv.1 hU.1 hV.1
  have hii := hu.2.mul hp hpm hv.2 hU.2 hV.2
  have hri := hu.1.mul hp hpm hv.2 hU.1 hV.2
  have hir := hu.2.mul hp hpm hv.1 hU.2 hV.1
  have hR := mulCutBits_properCut _ _ m hU.1 hV.1
  have hI := mulCutBits_properCut _ _ m hU.2 hV.2
  have hRI := mulCutBits_properCut _ _ m hU.1 hV.2
  have hIR := mulCutBits_properCut _ _ m hU.2 hV.1
  refine ⟨?_,?_⟩
  · simpa [ComplexBits.mul,Complex.mul_re,sub_eq_add_neg] using
      hrr.add hp hpm (hii.neg hpm hI) hR (negCutBits_properCut _ m hI)
  · simpa [ComplexBits.mul,Complex.mul_im,add_comm] using hri.add hp hpm hir hRI hIR

theorem ComplexDecisionTrace.normSq {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u : ComplexBits B} {x : ℂ}
    (hu : ComplexDecisionTrace p u x) (hU : u.CutOn m) :
    CutDecisionTrace p u.normSq (Complex.normSq x) := by
  have hr := hu.1.mul hp hpm hu.1 hU.1 hU.1
  have hi := hu.2.mul hp hpm hu.2 hU.2 hU.2
  simpa [ComplexBits.normSq,Complex.normSq_apply] using
    hr.add hp hpm hi (mulCutBits_properCut _ _ m hU.1 hU.1) (mulCutBits_properCut _ _ m hU.2 hU.2)

theorem ComplexDecisionTrace.power {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u : ComplexBits B} {x : ℂ}
    (hu : ComplexDecisionTrace p u x) (hU : u.CutOn m) (n : ℕ) :
    ComplexDecisionTrace p (u.power n) (x^n) := by
  induction n with
  | zero => simpa [ComplexBits.power] using ComplexDecisionTrace.ofNat p 1
  | succ n ih =>
    simpa [ComplexBits.power,pow_succ] using ih.mul hp hpm hu (ComplexBits.power_cutOn hU n) hU

theorem taylorPrefix_decisionTrace {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m)
    {A : ℕ → ComplexBits B} {a : ℕ → ℂ} {Z : ComplexBits B} {z : ℂ}
    (hA : ∀ n, (A n).CutOn m) (ha : ∀ n, ComplexDecisionTrace p (A n) (a n))
    (hZ : Z.CutOn m) (hz : ComplexDecisionTrace p Z z) (N : ℕ) :
    ComplexDecisionTrace p (taylorPrefixBits A Z N) (JSP000930.Analytic.partialSum a z N) := by
  induction N with
  | zero =>
    simpa [taylorPrefixBits,JSP000930.Analytic.partialSum] using ComplexDecisionTrace.ofNat p 0
  | succ N ih =>
    have htN := taylorPrefixBits_cutOn (a := A) hZ (m := N) (fun i _ => hA i) N le_rfl
    have hpA := (ha N).mul hp hpm (hz.power hp hpm hZ N) (hA N) (ComplexBits.power_cutOn hZ N)
    have hpB := ComplexBits.mul_cutOn (hA N) (ComplexBits.power_cutOn hZ N)
    simpa [taylorPrefixBits,JSP000930.Analytic.partialSum,Finset.sum_range_succ] using
      ih.add hp hpm hpA htN hpB

theorem trace_complex_eq {p : ℕ → B} (hp : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m)
    {u v : ComplexBits B} {x y : ℂ}
    (hu : ComplexDecisionTrace p u x) (hv : ComplexDecisionTrace p v y)
    (he : m ≤ u.name =ᴮ v.name) : x = y := by
  rw [ComplexBits.name_eq] at he
  apply Complex.ext
  · exact trace_cut_eq hp hnz hpm hu.1 hv.1 (he.trans inf_le_left)
  · exact trace_cut_eq hp hnz hpm hu.2 hv.2 (he.trans inf_le_right)

end JSP000930.BooleanAnalysis
