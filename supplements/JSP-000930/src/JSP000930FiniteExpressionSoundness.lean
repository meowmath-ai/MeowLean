import JSP000930FixedReciprocalMargins

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B] [Countable V] [Nonempty V]

theorem exists_expr_decision_completion (u : V → ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hu : ∀ i, (u i).CutOn m) (l : List (Expr V))
    (h : ∀ e ∈ l, e.Safe u m) :
    ∃ (p : ℕ → B) (w : V → ℂ), Antitone p ∧ (∀ n,p n ≠ ⊥) ∧
      (∀ n,p n ≤ m) ∧ (∀ i, ComplexDecisionTrace p (u i) (w i)) ∧
      ∀ e ∈ l, ComplexDecisionTrace p (e.eval u) (e.evalGround w) := by
  let D := l.flatMap Expr.denominators
  have hD : ∀ d ∈ D, m ≤ positiveCutValue (d.eval u).normSq := by
    intro d hd
    obtain ⟨e,he,hdE⟩ := List.mem_flatMap.mp hd
    exact h e he d hdE
  obtain ⟨k,hk,hkm,hK⟩ := exists_fixedMargins u D m hm hD
  have huK : ∀ i, (u i).CutOn k := fun i =>
    ⟨properCutOn_mono hkm (hu i).1, properCutOn_mono hkm (hu i).2⟩
  obtain ⟨p,w,hp,hnz,hpk,ht⟩ := exists_complex_decision_completion u k hk huK
  refine ⟨p,w,hp,hnz,fun n => (hpk n).trans hkm,ht,?_⟩
  intro e he
  exact Expr.trace_eval_of_fixedMargins hp hnz hpk huK ht e
    (fun d hd => hK d (List.mem_flatMap.mpr ⟨e,he,hd⟩))

theorem expr_eq_forced (u : V → ComplexBits B) (m : B) (a b : Expr V)
    (hu : ∀ i, (u i).CutOn m) (ha : a.Safe u m) (hb : b.Safe u m)
    (hLaw : ∀ (p : ℕ → B) (w : V → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
      (∀ n,p n ≤ m) → (∀ i, ComplexDecisionTrace p (u i) (w i)) →
      a.evalGround w = b.evalGround w) :
    m ≤ (a.eval u).name =ᴮ (b.eval u).name := by
  by_contra hF
  obtain ⟨s,hs,hsm,hSep⟩ :=
    complex_eq_fail_survives (a.eval_cutOn u m hu ha) (b.eval_cutOn u m hu hb) hF
  have huS : ∀ i, (u i).CutOn s := fun i =>
    ⟨properCutOn_mono hsm (hu i).1, properCutOn_mono hsm (hu i).2⟩
  have hL : ∀ e ∈ [a,b], e.Safe u s := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl|rfl
    · exact Expr.safe_mono ha hsm
    · exact Expr.safe_mono hb hsm
  obtain ⟨p,w,hp,hnz,hps,ht,htE⟩ := exists_expr_decision_completion u s hs huS [a,b] hL
  have htA := htE a (by simp)
  have htB := htE b (by simp)
  exact hSep hp hnz hps htA htB (hLaw p w hp hnz (fun n => (hps n).trans hsm) ht)

theorem expr_distance_forced (u : V → ComplexBits B) (m : B) (a b : Expr V) (e : ℚ)
    (hu : ∀ i, (u i).CutOn m) (ha : a.Safe u m) (hb : b.Safe u m)
    (he : 0 ≤ e)
    (hLaw : ∀ (p : ℕ → B) (w : V → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
      (∀ n,p n ≤ m) → (∀ i, ComplexDecisionTrace p (u i) (w i)) →
      dist (a.evalGround w) (b.evalGround w) ≤ (e : ℝ)) :
    m ≤ distanceLe (a.eval u) (b.eval u) e := by
  by_contra hF
  have haV := a.eval_cutOn u m hu ha
  have hbV := b.eval_cutOn u m hu hb
  obtain ⟨s,hs,hsm,hSep⟩ := cut_order_fail_survives (proper_distanceCut haV hbV) hF
  have huS : ∀ i, (u i).CutOn s := fun i =>
    ⟨properCutOn_mono hsm (hu i).1, properCutOn_mono hsm (hu i).2⟩
  have hL : ∀ e ∈ [a,b], e.Safe u s := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl|rfl
    · exact Expr.safe_mono ha hsm
    · exact Expr.safe_mono hb hsm
  obtain ⟨p,w,hp,hnz,hps,ht,htE⟩ := exists_expr_decision_completion u s hs huS [a,b] hL
  have hpm : ∀ n, p n ≤ m := fun n => (hps n).trans hsm
  have htA := htE a (by simp)
  have htB := htE b (by simp)
  have hStrict := hSep hp hnz hps (trace_distanceCut hp hpm haV hbV htA htB)
    (checkedRealBits_traces p ((e : ℝ)^2))
  exact (not_le_of_gt hStrict) (pow_le_pow_left₀ dist_nonneg (hLaw p w hp hnz hpm ht) 2)

end JSP000930.Negative
