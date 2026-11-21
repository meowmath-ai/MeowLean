import JSP000930AnalyticDecisionCompletion

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem directedNear_countercell {m : B} {u v : RatPresentation → B} {ε : ℚ}
    (h : ¬ m ≤ directedNear u v ε) :
    ∃ (q r : RatPresentation) (s : B), s ≠ ⊥ ∧ s ≤ m ∧ ε ≤ r.value-q.value ∧
      s ≤ u r ∧ s ≤ (v q)ᶜ := by
  have hf : ¬ ∀ (q r : RatPresentation), ε ≤ r.value-q.value → m ⊓ u r ≤ v q := by
    intro hh
    exact h (directedNear_intro hh)
  push Not at hf
  obtain ⟨q,r,hqr,hbad⟩ := hf
  let s := (m ⊓ u r) ⊓ (v q)ᶜ
  have hs : s ≠ ⊥ := by
    intro he
    have hd : Disjoint (m ⊓ u r) (v q)ᶜ := disjoint_iff_inf_le.mpr (le_of_eq he)
    exact hbad (by simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr hd))
  exact ⟨q,r,s,hs,inf_le_left.trans inf_le_left,hqr,inf_le_left.trans inf_le_right,inf_le_right⟩

theorem trace_directedNear {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ} {ε : ℚ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (hm : m ≤ directedNear u v ε) : x-y ≤ (ε : ℝ) := by
  by_contra hh
  let δ := (x-y-(ε : ℝ))/3
  have hd : 0 < δ := by dsimp [δ]; linarith [lt_of_not_ge hh]
  obtain ⟨q0,hql,hqu⟩ := exists_rat_btwn (show y < y+δ by linarith)
  obtain ⟨r0,hrl,hru⟩ := exists_rat_btwn (show x-δ < x by linarith)
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective q0
  obtain ⟨r,hr⟩ := ratPresentation_value_surjective r0
  have hdist : ε ≤ r.value-q.value := by
    have h' : (ε : ℝ) ≤ (r.value : ℝ)-(q.value : ℝ) := by
      rw [hq,hr]
      dsimp [δ] at hqu hrl
      linarith
    exact_mod_cast h'
  obtain ⟨n,hn⟩ := eventuallyMeet h (hu.below r (by rwa [hr])) (hv.above q (by rwa [hq]))
  have huq := (le_inf (hpm n) (hn.trans inf_le_left)).trans (directedNear_project hm q r hdist)
  exact hnz n (le_bot_iff.mp ((le_inf huq (hn.trans inf_le_right)).trans (by simp)))

theorem trace_cutNear {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ} {ε : ℚ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (hm : m ≤ cutNear u v ε) : |x-y| ≤ (ε : ℝ) := by
  rw [abs_le]
  constructor
  · linarith [trace_directedNear h hnz hpm hv hu (hm.trans inf_le_right)]
  · exact trace_directedNear h hnz hpm hu hv (hm.trans inf_le_left)

theorem trace_directedNear_failure_forces_gap {p : ℕ → B} (h : Antitone p)
    (hnz : ∀ n, p n ≠ ⊥) {u v : RatPresentation → B} {x y : ℝ} {ε : ℚ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (q r : RatPresentation) (hqr : ε ≤ r.value-q.value)
    (hlo : ∃ n, p n ≤ u r) (hhi : ∃ n, p n ≤ (v q)ᶜ) :
    (ε : ℝ) ≤ x-y := by
  have hr := trace_forcedMember_le h hnz hu r hlo
  have hq := trace_forcedAbsent_ge h hnz hv q hhi
  have hdist : (ε : ℝ) ≤ (r.value : ℝ)-(q.value : ℝ) := by exact_mod_cast hqr
  linarith

end JSP000930.BooleanAnalysis
