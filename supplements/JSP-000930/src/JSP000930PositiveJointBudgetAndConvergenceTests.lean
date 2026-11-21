import JSP000930PositiveTraceIdentifiesNativeTaylorLimit

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem pair_iSup_cover {I J : Type} (u : I → B) (v : J → B) (m : B)
    (hu : m ≤ ⨆ i,u i) (hv : m ≤ ⨆ j,v j) :
    m ≤ ⨆ ij : I × J,u ij.1 ⊓ v ij.2 := by
  apply (le_inf hu hv).trans
  rw [iSup_inf_iSup]

abbrev TaylorTraceTest := ℕ × (ℕ × ℕ)

def TaylorTraceTest.cutoff (T : TaylorTraceTest) (im : Bool) : ℕ :=
  if im then T.2.2 else T.2.1

noncomputable def convergenceTestValue (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (k : ℕ) (im : Bool) (N : ℕ) : B :=
  cutConvergesTail (fun n => (taylorPrefixBits A Z n).coord im)
    ((taylorLimitBits A Z).coord im) (traceTolerance k) N

noncomputable def TaylorTraceTest.value (T : TaylorTraceTest)
    (A : ℕ → ComplexBits B) (Z : ComplexBits B) (k : ℕ) : B :=
  (⨅ n,radiusBudgetBits (A n) (k+1) T.1 n) ⊓
    (convergenceTestValue A Z k false T.2.1 ⊓ convergenceTestValue A Z k true T.2.2)

theorem taylorTraceTests_cover (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hG : GrowthOn m A) (k : ℕ) :
    m ≤ ⨆ T : TaylorTraceTest,T.value A Z k := by
  have hc (im : Bool) : m ≤ ⨆ N : ℕ,convergenceTestValue A Z k im N :=
    taylorLimitBits_converges A Z m hA hZ hG im (traceTolerance k) (traceTolerance_positive k)
  exact pair_iSup_cover (fun K => ⨅ n,radiusBudgetBits (A n) (k+1) K n)
    (fun r : ℕ × ℕ => convergenceTestValue A Z k false r.1 ⊓ convergenceTestValue A Z k true r.2)
    m (hG (k+1) (by omega))
    (pair_iSup_cover (convergenceTestValue A Z k false) (convergenceTestValue A Z k true)
      m (hc false) (hc true))

theorem TaylorTraceTest.select_cutoff {T : TaylorTraceTest}
    {A : ℕ → ComplexBits B} {Z : ComplexBits B} {k : ℕ} {p : B}
    (hp : p ≤ T.value A Z k) (im : Bool) :
    p ≤ convergenceTestValue A Z k im (T.cutoff im) := by
  cases im
  · exact hp.trans (inf_le_right.trans inf_le_left)
  · exact hp.trans (inf_le_right.trans inf_le_right)

theorem selected_tests_yield_radiusCode
    {p : ℕ → B} (hAnti : Antitone p) (hNZ : ∀ n,p n ≠ ⊥)
    {m : B} (hm : ∀ n,p n ≤ m)
    (A : ℕ → ComplexBits B) (a : ℕ → ℂ) (Z : ComplexBits B)
    (hA : ∀ n,(A n).CutOn m) (ha : ∀ n,ComplexDecisionTrace p (A n) (a n))
    (T : ℕ → TaylorTraceTest) (hT : ∀ k,p k ≤ (T k).value A Z k) :
    RadiusCode a := by
  intro R hR
  let k := R-1
  have hEq : k+1 = R := by dsimp only [k]; omega
  refine ⟨(T k).1,fun n => ?_⟩
  rw [← hEq]
  exact trace_budget_to_norm (trace_radiusBudget_at hAnti hNZ hm (ha n) (hA n)
    (((hT k).trans inf_le_left).trans (iInf_le _ n)))

end JSP000930.Positive
