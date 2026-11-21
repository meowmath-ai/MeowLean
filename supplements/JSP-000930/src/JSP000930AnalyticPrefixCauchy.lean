import JSP000930AnalyticRadiusTrace

open Lattice Filter
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def halfRadiusBound (z : ComplexBits B) (R : ℕ) : B :=
  weightedRationalSet z.normSq ⊆ᴮ weightedRationalSet (checkedRealBits (((R : ℝ)/2)^2))

theorem trace_halfRadius_bound {p : ℕ → B} (hp : Antitone p)
    (hnz : ∀ n,p n ≠ ⊥) {m : B} (hpm : ∀ n, p n ≤ m)
    {Z : ComplexBits B} {z : ℂ} (hZ : Z.CutOn m) (hz : ComplexDecisionTrace p Z z)
    {R : ℕ} (hR : m ≤ halfRadiusBound Z R) : ‖z‖ ≤ (R : ℝ)/2 := by
  have qs := trace_subset_le hp hnz hpm (hz.normSq hp hpm hZ)
    (checkedRealBits_traces p (((R : ℝ)/2)^2)) hR
  rw [Complex.normSq_eq_norm_sq] at qs
  have hr : 0 ≤ (R : ℝ)/2 := by positivity
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

private theorem tailBudget_uniform_threshold (K : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ N : ℕ, ∀ i, N ≤ i → tailBudget K i < ε/2 := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (tendsto_tailBudget_zero K)
    (ε/2) (by positivity)
  refine ⟨N,fun i hi => ?_⟩
  have h := hN i hi
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold tailBudget; positivity)] at h
  exact h

private theorem prefix_distance_lt {a : ℕ → ℂ} (ha : RadiusCode a)
    {R K i j : ℕ} {z : ℂ} (hK : ∀ n, ‖a n‖*(R : ℝ)^n ≤ (K : ℝ))
    (hZ : ‖z‖ ≤ (R : ℝ)/2) {ε : ℝ}
    (hi : tailBudget K i < ε/2) (hj : tailBudget K j < ε/2) :
    dist (partialSum a z i) (partialSum a z j) < ε := by
  have hI := evaluate_sub_partialSum_le ha hK hZ i
  have hJ := evaluate_sub_partialSum_le ha hK hZ j
  have hD := dist_triangle (partialSum a z i) (evaluate a z) (partialSum a z j)
  rw [dist_comm (partialSum a z i) (evaluate a z)] at hD
  simp only [dist_eq_norm] at hD ⊢
  linarith

def ComplexBits.coord (u : ComplexBits B) (im : Bool) : RatPresentation → B :=
  if im then u.im else u.re

def complexCoord (x : ℂ) (im : Bool) : ℝ :=
  if im then x.im else x.re

private theorem complexCoord_absDiff_le (x y : ℂ) (im : Bool) :
    |complexCoord x im-complexCoord y im| ≤ dist x y := by
  cases im
  · simpa [complexCoord,dist_eq_norm,Complex.sub_re] using Complex.abs_re_le_norm (x-y)
  · simpa [complexCoord,dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (x-y)

theorem ComplexDecisionTrace.coordinate {p : ℕ → B} {A : ComplexBits B} {a : ℂ}
    (h : ComplexDecisionTrace p A a) (im : Bool) :
    CutDecisionTrace p (A.coord im) (complexCoord a im) := by
  cases im
  · exact h.1
  · exact h.2

theorem forced_prefixDirectedNear_of_budget (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hGrowth : GrowthOn m A)
    (R K : ℕ) (hR : m ≤ halfRadiusBound Z R)
    (hK : ∀ n,m ≤ radiusBudgetBits (A n) R K n) (i j : ℕ) (im : Bool) (ε : ℚ)
    (hi : tailBudget K i < (ε : ℝ)/2) (hj : tailBudget K j < (ε : ℝ)/2) :
    m ≤ directedNear ((taylorPrefixBits A Z i).coord im) ((taylorPrefixBits A Z j).coord im) ε := by
  by_contra h
  obtain ⟨q,r,s,hs,hsm,hqr,hlo,hhi⟩ := directedNear_countercell h
  have hA' (n : ℕ) : (A n).CutOn s :=
    ⟨properCutOn_mono hsm (hA n).1,properCutOn_mono hsm (hA n).2⟩
  have hZ' : Z.CutOn s := ⟨properCutOn_mono hsm hZ.1,properCutOn_mono hsm hZ.2⟩
  obtain ⟨p,a,z,hp,hnz,hps,ha,hz,hRa⟩ :=
    entireDecisionTrace_completion A Z s hs hA' hZ' (hGrowth.mono hsm)
  have hz' := trace_halfRadius_bound hp hnz hps hZ' hz (hsm.trans hR)
  have hKa (n : ℕ) : ‖a n‖*(R : ℝ)^n ≤ (K : ℝ) :=
    trace_budget_to_norm (trace_radiusBudget_at hp hnz hps (ha n) (hA' n)
      ((hps 0).trans (hsm.trans (hK n))))
  have hUV := prefix_distance_lt hRa hKa hz' hi hj
  have htI := (taylorPrefix_decisionTrace hp hps hA' ha hZ' hz i).coordinate im
  have htJ := (taylorPrefix_decisionTrace hp hps hA' ha hZ' hz j).coordinate im
  have hGap := trace_directedNear_failure_forces_gap hp hnz htI htJ q r hqr
    ⟨0,(hps 0).trans hlo⟩ ⟨0,(hps 0).trans hhi⟩
  have hN := complexCoord_absDiff_le (partialSum a z i) (partialSum a z j) im
  exact (not_lt_of_ge (hGap.trans ((le_abs_self _).trans hN))) hUV

theorem forced_prefixCauchy_of_budget (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) (hA : ∀ n,(A n).CutOn m) (hZ : Z.CutOn m) (hGrowth : GrowthOn m A)
    (R K : ℕ) (hR : m ≤ halfRadiusBound Z R)
    (hK : ∀ n,m ≤ radiusBudgetBits (A n) R K n) (im : Bool)
    (ε : ℚ) (he : 0 < ε) :
    ∃ N : ℕ, m ≤ cutCauchyTail (fun n => (taylorPrefixBits A Z n).coord im) ε N := by
  obtain ⟨N,hN⟩ := tailBudget_uniform_threshold K (show (0 : ℝ) < (ε : ℝ) by exact_mod_cast he)
  refine ⟨N,?_⟩
  unfold cutCauchyTail
  refine le_iInf fun i => le_iInf fun j => le_inf ?_ ?_
  · exact forced_prefixDirectedNear_of_budget A Z m hA hZ hGrowth R K hR hK
      i.val j.val im ε (hN i.val i.property) (hN j.val j.property)
  · exact forced_prefixDirectedNear_of_budget A Z m hA hZ hGrowth R K hR hK
      j.val i.val im ε (hN j.val j.property) (hN i.val i.property)

end JSP000930.BooleanAnalysis
