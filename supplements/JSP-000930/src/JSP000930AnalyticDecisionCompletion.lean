import JSP000930AnalyticComplexTrace
import JSP000930PositiveRationalCompletionDecisionTrace

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Positive

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] [Countable J] [Nonempty J]

theorem mixed_cut_decision_completion {X : ℕ → Type}
    (β : J → RatPresentation → B) (m : B) (hm : m ≠ ⊥)
    (hβ : ∀ j, ProperCutOn m (β j))
    (V : ∀ n,X n → B) (hV : ∀ n,m ≤ ⨆ x,V n x) :
    ∃ (p : ℕ → B) (select : ∀ n,X n) (z : J → ℝ),
      Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ m) ∧
      (∀ n,p n ≤ V n (select n)) ∧ ∀ j, CutDecisionTrace p (β j) (z j) := by
  obtain ⟨p,sel,z,box,hanti,hnz,hm',hsel,hbox⟩ :=
    mixed_cut_ground_completion β m hm hβ V hV
  refine ⟨p,sel,z,hanti,hnz,hm',hsel,fun j => ?_⟩
  obtain ⟨hlo,hhi⟩ := completion_decides_strict_rational_tests (hβ j) p
    (cutCoordIndex j) hm' (box j) (z j) (hbox j)
  exact ⟨hlo,hhi⟩

theorem trace_forcedMember_le {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {u : RatPresentation → B} {x : ℝ} (hu : CutDecisionTrace p u x)
    (q : RatPresentation) (hq : ∃ n, p n ≤ u q) : (q.value : ℝ) ≤ x := by
  by_contra hx
  obtain ⟨n,hn⟩ := eventuallyMeet h hq (hu.above q (lt_of_not_ge hx))
  exact hnz n (le_bot_iff.mp (hn.trans (by simp)))

theorem trace_forcedAbsent_ge {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {u : RatPresentation → B} {x : ℝ} (hu : CutDecisionTrace p u x)
    (q : RatPresentation) (hq : ∃ n, p n ≤ (u q)ᶜ) : x ≤ (q.value : ℝ) := by
  by_contra hx
  obtain ⟨n,hn⟩ := eventuallyMeet h (hu.below q (lt_of_not_ge hx)) hq
  exact hnz n (le_bot_iff.mp (hn.trans (by simp)))

theorem nonzero_cut_order_countercell {m : B} {u v : RatPresentation → B}
    (hu : ProperCutOn m u) (h : ¬ m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v) :
    ∃ (q r : RatPresentation) (s : B), s ≠ ⊥ ∧ s ≤ m ∧ q.value < r.value ∧
      s ≤ u r ∧ s ≤ (v q)ᶜ := by
  rw [weightedRationalSet_subset] at h
  have failed : ∃ q, ¬ m ≤ imp (u q) (v q) := by
    by_contra hf
    push Not at hf
    exact h (le_iInf hf)
  obtain ⟨q,hq⟩ := failed
  let cell := m ⊓ u q ⊓ (v q)ᶜ
  have hcell : cell ≠ ⊥ := by
    intro he
    apply hq
    rw [← deduction]
    have hd : Disjoint (m ⊓ u q) (v q)ᶜ := disjoint_iff_inf_le.mpr (le_of_eq he)
    simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr hd)
  have hbound : cell ≤ ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), u r :=
    (inf_le_left : cell ≤ m ⊓ u q).trans (hu.2.2.2 q)
  have hnot : ¬ ∀ (r : RatPresentation), q.value < r.value → cell ⊓ u r = ⊥ := by
    intro he
    apply hcell
    apply le_bot_iff.mp
    apply (le_inf le_rfl hbound).trans
    rw [inf_iSup_eq]
    refine iSup_le fun r => ?_
    rw [inf_iSup_eq]
    exact iSup_le fun hr => le_of_eq (he r hr)
  push Not at hnot
  obtain ⟨r,hqr,hr⟩ := hnot
  exact ⟨q,r,cell ⊓ u r,hr,inf_le_left.trans (inf_le_left.trans inf_le_left),
    hqr,inf_le_right,inf_le_left.trans inf_le_right⟩

end JSP000930.BooleanAnalysis
