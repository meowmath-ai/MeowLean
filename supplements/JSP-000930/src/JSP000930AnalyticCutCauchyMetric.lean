import JSP000930AnalyticCutCauchy

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanNames JSP000933.PositiveForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def checkedRealBits (x : ℝ) (q : RatPresentation) : B :=
  crispTruth B ((q.value : ℝ) < x)

theorem directedNear_checkedRealBits (x y : ℝ) (ε : ℚ) :
    directedNear (checkedRealBits (B := B) x) (checkedRealBits y) ε =
      crispTruth B (x-y ≤ (ε : ℝ)) := by
  by_cases h : x-y ≤ (ε : ℝ)
  · simp only [crispTruth, h, ite_true]
    apply top_unique
    apply directedNear_intro
    intro q r hqr
    have hrq : (ε : ℝ) ≤ (r.value : ℝ)-(q.value : ℝ) := by exact_mod_cast hqr
    by_cases hr : (r.value : ℝ) < x
    · have hq : (q.value : ℝ) < y := by linarith
      simp [checkedRealBits, crispTruth, hq]
    · simp [checkedRealBits, crispTruth, hr]
  · simp only [crispTruth, h, ite_false]
    let Δ := x-y-(ε : ℝ)
    have hΔ : 0 < Δ := by dsimp [Δ]; linarith
    obtain ⟨q0,hq₁,hq₂⟩ := exists_rat_btwn (show y < y+Δ/4 by linarith)
    obtain ⟨r0,hr₁,hr₂⟩ := exists_rat_btwn (show x-Δ/4 < x by linarith)
    obtain ⟨q,hq⟩ := ratPresentation_value_surjective q0
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective r0
    have hz : (ε : ℝ) ≤ (r.value : ℝ)-(q.value : ℝ) := by
      rw [hq,hr]
      dsimp [Δ] at hq₂ hr₁
      linarith
    have hzr : ε ≤ r.value-q.value := by exact_mod_cast hz
    have hq' : ¬ (q.value : ℝ) < y := by rw [hq]; exact not_lt_of_ge hq₁.le
    have hr' : (r.value : ℝ) < x := by rw [hr]; exact hr₂
    have hc := directedNear_project
      (p := directedNear (checkedRealBits (B := B) x) (checkedRealBits y) ε)
      le_rfl q r hzr
    simp only [checkedRealBits, crispTruth, hq', hr', ite_true, ite_false, inf_top_eq] at hc
    exact le_bot_iff.mp hc

theorem cutNear_checkedRealBits (x y : ℝ) (ε : ℚ) :
    cutNear (checkedRealBits (B := B) x) (checkedRealBits y) ε =
      crispTruth B (|x-y| ≤ (ε : ℝ)) := by
  rw [cutNear, directedNear_checkedRealBits, directedNear_checkedRealBits]
  have he : |x-y| ≤ (ε : ℝ) ↔
      x-y ≤ (ε : ℝ) ∧ y-x ≤ (ε : ℝ) := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he]
  by_cases hx : x-y ≤ (ε : ℝ) <;> by_cases hy : y-x ≤ (ε : ℝ) <;>
    simp [crispTruth, hx, hy]

end JSP000930.BooleanAnalysis
