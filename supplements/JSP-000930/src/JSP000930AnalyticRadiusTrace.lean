import JSP000930AnalyticTraceMetric
import JSP000930AnalyticTaylorTail

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def radiusBudgetBits (a : ComplexBits B) (R K n : ℕ) : B :=
  weightedRationalSet (mulCutBits a.normSq (checkedRealBits (((R : ℝ)^n)^2))) ⊆ᴮ
    weightedRationalSet (checkedRealBits ((K : ℝ)^2))

def GrowthOn (m : B) (a : ℕ → ComplexBits B) : Prop :=
  ∀ R : ℕ, 1 ≤ R → m ≤ ⨆ K : ℕ, ⨅ n : ℕ, radiusBudgetBits (a n) R K n

theorem GrowthOn.mono {m m' : B} {a : ℕ → ComplexBits B} (h : GrowthOn m a)
    (hm : m' ≤ m) : GrowthOn m' a :=
  fun R hR => hm.trans (h R hR)

theorem CutDecisionTrace.tail {p : ℕ → B} (hp : Antitone p) (k : ℕ)
    {u : RatPresentation → B} {x : ℝ} (h : CutDecisionTrace p u x) :
    CutDecisionTrace (fun n => p (n+k)) u x := by
  constructor
  · intro q hq
    obtain ⟨n,hn⟩ := h.below q hq
    exact ⟨n,(hp (Nat.le_add_right n k)).trans hn⟩
  · intro q hq
    obtain ⟨n,hn⟩ := h.above q hq
    exact ⟨n,(hp (Nat.le_add_right n k)).trans hn⟩

theorem trace_radiusBudget_at {p : ℕ → B} (hp : Antitone p)
    (hnz : ∀ n, p n ≠ ⊥) {m : B} (hpm : ∀ n, p n ≤ m)
    {a : ComplexBits B} {z : ℂ} (ht : ComplexDecisionTrace p a z)
    (ha : a.CutOn m) {R K n k : ℕ} (hb : p k ≤ radiusBudgetBits a R K n) :
    Complex.normSq z * (((R : ℝ)^n)^2) ≤ (K : ℝ)^2 := by
  let r := ((R : ℝ)^n)^2
  let pp : ℕ → B := fun j => p (j+k)
  have ha' : Antitone pp := fun _ _ h => hp (Nat.add_le_add_right h k)
  have hl := (ht.normSq hp hpm ha).mul hp hpm (checkedRealBits_traces p r)
    (ComplexBits.normSq_cutOn ha) (properCutOn_mono le_top (checkedRealBits_properCut r))
  exact trace_subset_le (p := pp) ha' (fun j => hnz (j+k))
    (fun j => hp (Nat.le_add_left k j)) (hl.tail hp k)
    ((checkedRealBits_traces p ((K : ℝ)^2)).tail hp k) hb

theorem trace_budget_to_norm {z : ℂ} {R K n : ℕ}
    (h : Complex.normSq z * (((R : ℝ)^n)^2) ≤ (K : ℝ)^2) :
    ‖z‖ * (R : ℝ)^n ≤ (K : ℝ) := by
  rw [Complex.normSq_eq_norm_sq,← mul_pow] at h
  have hz : 0 ≤ ‖z‖ * (R : ℝ)^n := by positivity
  have hk : 0 ≤ (K : ℝ) := by positivity
  nlinarith

theorem entireDecisionTrace_completion (A : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) (hm : m ≠ ⊥) (hA : ∀ n, (A n).CutOn m)
    (hZ : Z.CutOn m) (hGrowth : GrowthOn m A) :
    ∃ (p : ℕ → B) (a : ℕ → ℂ) (z : ℂ),
      Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ m) ∧
      (∀ n,ComplexDecisionTrace p (A n) (a n)) ∧ ComplexDecisionTrace p Z z ∧ RadiusCode a := by
  let Q : Option ℕ → ComplexBits B := fun i => match i with
    | none => Z
    | some n => A n
  let β : Option ℕ × Bool → RatPresentation → B := fun j =>
    if j.2 then (Q j.1).im else (Q j.1).re
  let V (k K : ℕ) : B := ⨅ n : ℕ, radiusBudgetBits (A n) (k+1) K n
  have hβ (j : Option ℕ × Bool) : ProperCutOn m (β j) := by
    rcases j with ⟨i,b⟩
    cases i with
    | none => cases b
              · exact hZ.1
              · exact hZ.2
    | some n => cases b
                · exact (hA n).1
                · exact (hA n).2
  have hv (k : ℕ) : m ≤ ⨆ K : ℕ, V k K := hGrowth (k+1) (by omega)
  obtain ⟨p,K,w,hp,hnz,hpm,hsel,ht⟩ :=
    mixed_cut_decision_completion β m hm hβ V hv
  let z : ℂ := ⟨w (none,false),w (none,true)⟩
  let a (n : ℕ) : ℂ := ⟨w (some n,false),w (some n,true)⟩
  have htA (n : ℕ) : ComplexDecisionTrace p (A n) (a n) :=
    ⟨ht (some n,false),ht (some n,true)⟩
  have htZ : ComplexDecisionTrace p Z z := ⟨ht (none,false),ht (none,true)⟩
  refine ⟨p,a,z,hp,hnz,hpm,htA,htZ,(squaredRadiusCode_iff a).1 ?_⟩
  intro R hR
  let k := R-1
  have hk : k+1 = R := by dsimp [k]; omega
  refine ⟨K k,fun n => ?_⟩
  have hb : p k ≤ radiusBudgetBits (A n) R (K k) n := by
    rw [← hk]
    exact (hsel k).trans (iInf_le _ n)
  exact trace_radiusBudget_at hp hnz hpm (htA n) (hA n) hb

end JSP000930.BooleanAnalysis
