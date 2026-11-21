import JSP000930PositiveCommonComplexDecisionCompletion

open Filter

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def traceTolerance (n : ℕ) : ℚ := (1/2)^n

theorem traceTolerance_positive (n : ℕ) : 0 < traceTolerance n := by
  unfold traceTolerance
  positivity

theorem traceTolerance_eventually_lt {ε : ℝ} (h : 0 < ε) :
    ∃ n, (traceTolerance n : ℝ) < ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one h (show (1/2 : ℝ) < 1 by norm_num)
  refine ⟨n,?_⟩
  simpa [traceTolerance] using hn

theorem trace_coord {p : ℕ → B} {Z : ComplexBits B} {z : ℂ}
    (h : ComplexDecisionTrace p Z z) (b : Bool) :
    CutDecisionTrace p (Z.coord b) (complexSide z b) := by
  cases b
  · exact h.1
  · exact h.2

theorem trace_identifies_taylorLimit
    {p : ℕ → B} (hAnti : Antitone p) (hNZ : ∀ n,p n ≠ ⊥)
    {m : B} (hm : ∀ n,p n ≤ m)
    (A : ℕ → ComplexBits B) (a : ℕ → ℂ) (Z : ComplexBits B) (z y : ℂ)
    (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m)
    (hta : ∀ n,ComplexDecisionTrace p (A n) (a n))
    (htz : ComplexDecisionTrace p Z z)
    (hty : ComplexDecisionTrace p (taylorLimitBits A Z) y)
    (hR : RadiusCode a) (select : ℕ → Bool → ℕ)
    (hSel : ∀ k b,p k ≤ cutConvergesTail (fun n => (taylorPrefixBits A Z n).coord b)
      ((taylorLimitBits A Z).coord b) (traceTolerance k) (select k b)) :
    evaluate a z = y := by
  have hClose (b : Bool) {ε : ℝ} (hε : 0 < ε) :
      ∃ N : ℕ,∀ n ≥ N,dist (complexSide (partialSum a z n) b) (complexSide y b) < ε := by
    obtain ⟨k,hk⟩ := traceTolerance_eventually_lt hε
    refine ⟨select k b,fun n hn => ?_⟩
    have hNear : p k ≤ cutNear ((taylorPrefixBits A Z n).coord b)
      ((taylorLimitBits A Z).coord b) (traceTolerance k) :=
      (hSel k b).trans (iInf_le _ (⟨n,hn⟩ : {j : ℕ // select k b ≤ j}))
    have hp' : Antitone (fun j => p (j+k)) := fun i j hij => hAnti (Nat.add_le_add_right hij k)
    have hPref := trace_coord (taylorPrefix_decisionTrace hAnti hm hA hta hZ htz n) b
    have hLim := trace_coord hty b
    have hDist := trace_cutNear hp' (fun j => hNZ (j+k))
      (fun j => hAnti (Nat.le_add_left k j))
      (hPref.tail hAnti k) (hLim.tail hAnti k) hNear
    rw [Real.dist_eq]
    exact hDist.trans_lt hk
  have hLimit (b : Bool) :
      Tendsto (fun n => complexSide (partialSum a z n) b) atTop (nhds (complexSide y b)) :=
    Metric.tendsto_atTop.mpr fun ε hε => hClose b hε
  have hGround : Tendsto (fun n => partialSum a z n) atTop (nhds (evaluate a z)) := by
    simpa only [partialSum] using (hasSum_evaluate hR z).tendsto_sum_nat
  apply Complex.ext
  · exact tendsto_nhds_unique (Complex.continuous_re.continuousAt.tendsto.comp hGround)
      (hLimit false)
  · exact tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hGround)
      (hLimit true)

end JSP000930.Positive
