import JSP000930NegativeFinitePolynomialGrowth

open Fol Lattice
open scoped Flypitch bSet BigOperators

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem partialSum_succ_shift (w : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    partialSum w z (n+1) = w 0 + z*partialSum (fun i => w (i+1)) z n := by
  unfold partialSum
  rw [Finset.sum_range_succ']
  simp only [pow_succ,pow_zero,mul_one,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem trace_mixedPolynomialEval_zeroPadded {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n,p n ≤ m)
    (f : List (ComplexBits B)) (w : ℕ → ℂ) (z : ComplexBits B) (v : ℂ)
    (hf : ∀ c ∈ f,c.CutOn m) (hF : ∀ n,ComplexDecisionTrace p (zeroPaddedPoly f n) (w n))
    (hz : z.CutOn m) (hZ : ComplexDecisionTrace p z v) :
    ComplexDecisionTrace p (mixedPolynomialEval f z) (partialSum w v f.length) := by
  induction f generalizing w with
  | nil => simpa [mixedPolynomialEval,partialSum] using ComplexDecisionTrace.ofNat p 0
  | cons c f ih =>
    have hc := hf c List.mem_cons_self
    have hF0 : ComplexDecisionTrace p c (w 0) := hF 0
    have htail : ∀ d ∈ f,d.CutOn m := fun d hd => hf d (List.mem_cons_of_mem _ hd)
    have hT0 (i : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly f i) (w (i+1)) := hF (i+1)
    have hTail := ih (fun i => w (i+1)) htail hT0
    have ht := mixedPolynomialEval_cutOn f z htail hz
    have hP := hZ.mul hp hpm hTail hz ht
    have hQ := hF0.add hp hpm hP hc (ComplexBits.mul_cutOn hz ht)
    simpa only [mixedPolynomialEval,List.foldr_cons,List.length_cons,partialSum_succ_shift] using hQ

theorem zeroPaddedPoly_prefix_eq_horner (f : List (ComplexBits B))
    (z : ComplexBits B) (m : B) (hf : ∀ c ∈ f,c.CutOn m) (hz : z.CutOn m)
    (N : ℕ) (hN : f.length ≤ N) :
    m ≤ (taylorPrefixBits (zeroPaddedPoly f) z N).name =ᴮ (mixedPolynomialEval f z).name := by
  let F (i : Option ℕ) : ComplexBits B := match i with
    | none => z
    | some n => zeroPaddedPoly f n
  have hF (i : Option ℕ) : (F i).CutOn m := by
    cases i with
    | none => exact hz
    | some n => exact zeroPaddedPoly_cutOn f m hf n
  have hPref := taylorPrefixBits_cutOn (a := zeroPaddedPoly f) hz
    (m := N) (fun i _ => zeroPaddedPoly_cutOn f m hf i) N le_rfl
  have hHorner := mixedPolynomialEval_cutOn f z hf hz
  refine complexEq_of_decision_law F m hF _ _ hPref hHorner ?_
  intro p w hp hn hpm ht
  let a (n : ℕ) := w (some n)
  have hA (n : ℕ) : ComplexDecisionTrace p (zeroPaddedPoly f n) (a n) := ht (some n)
  have hZ : ComplexDecisionTrace p z (w none) := ht none
  have hPlain : ∀ n ≥ f.length, a n = 0 := by
    intro n hn'
    have he : zeroPaddedPoly f n = ComplexBits.ofNat 0 :=
      padCoeff_eq_zero_after (ComplexBits.ofNat 0) f n hn'
    have hA' := hA n
    rw [he] at hA'
    have ht0 : ComplexDecisionTrace p (ComplexBits.ofNat 0) (0 : ℂ) := by
      simpa using ComplexDecisionTrace.ofNat p 0
    exact trace_complex_eq hp hn hpm hA' ht0 (le_top.trans bSet.bv_refl)
  have hSame : partialSum a (w none) N = partialSum a (w none) f.length := by
    unfold partialSum
    exact Finset.eventually_constant_sum (fun i hi => by simp [hPlain i hi]) hN
  refine ⟨partialSum a (w none) f.length,?_,
    trace_mixedPolynomialEval_zeroPadded hp hpm f a z (w none) hf hA hz hZ⟩
  rw [← hSame]
  exact taylorPrefix_decisionTrace hp hpm (zeroPaddedPoly_cutOn f m hf) hA hz hZ N

theorem cutNear_of_weighted_eq {m : B} {u v : RatPresentation → B} {ε : ℚ}
    (hu : ProperCutOn m u) (hv : ProperCutOn m v) (hε : 0 ≤ ε)
    (he : m ≤ weightedRationalSet u =ᴮ weightedRationalSet v) :
    m ≤ cutNear u v ε := by
  rw [weightedRationalSet_eq] at he
  refine le_inf (directedNear_intro ?_) (directedNear_intro ?_)
  · intro q r hqr
    have hv' := he.trans (inf_le_left.trans (iInf_le _ q))
    rw [← _root_.deduction] at hv'
    exact (le_inf inf_le_left (hu.2.2.1 q r (by linarith))).trans hv'
  · intro q r hqr
    have hu' := he.trans (inf_le_right.trans (iInf_le _ q))
    rw [← _root_.deduction] at hu'
    exact (le_inf inf_le_left (hv.2.2.1 q r (by linarith))).trans hu'

theorem zeroPaddedPoly_limit_eq_horner (f : List (ComplexBits B))
    (z : ComplexBits B) (m : B) (hf : ∀ c ∈ f,c.CutOn m) (hz : z.CutOn m) :
    m ≤ (taylorLimitBits (zeroPaddedPoly f) z).name =ᴮ (mixedPolynomialEval f z).name := by
  let a := zeroPaddedPoly f
  let u := taylorLimitBits a z
  let v := mixedPolynomialEval f z
  have hA := zeroPaddedPoly_cutOn f m hf
  have hG := zeroPaddedPoly_growth f m hf
  have hU := taylorLimitBits_cutOn a z m hA hz hG
  have hV := mixedPolynomialEval_cutOn f z hf hz
  have hh (x : ComplexBits B) (hx : x.CutOn m) (b : Bool) :
      ProperCutOn m (x.coord b) := by
    cases b
    · exact hx.1
    · exact hx.2
  have hComp (b : Bool) :
      m ≤ weightedRationalSet (u.coord b) =ᴮ weightedRationalSet (v.coord b) := by
    let q (n : ℕ) := (taylorPrefixBits a z n).coord b
    apply cutConverges_unique_name q (u.coord b) (v.coord b) m
      (fun e he => taylorLimitBits_converges a z m hA hz hG b e he) _
      (hh u hU b).2.2.2 (hh v hV b).2.2.2
    intro e he
    apply le_iSup_of_le f.length
    unfold cutConvergesTail
    refine le_iInf fun n => ?_
    have hPrefix := taylorPrefixBits_cutOn (a := a) hz (m := n.val) (fun j _ => hA j) n.val le_rfl
    have hSame := zeroPaddedPoly_prefix_eq_horner f z m hf hz n.val n.property
    rw [ComplexBits.name_eq] at hSame
    apply cutNear_of_weighted_eq (hh _ hPrefix b) (hh v hV b) he.le
    cases b
    · exact hSame.trans inf_le_left
    · exact hSame.trans inf_le_right
  rw [ComplexBits.name_eq]
  exact le_inf (hComp false) (hComp true)

end JSP000930.Negative
