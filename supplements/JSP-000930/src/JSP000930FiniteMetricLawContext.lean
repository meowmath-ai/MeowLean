import JSP000930NamedFinitePinValues

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B] [Countable V] [Nonempty V]

theorem expr_distance_forced_with_aux (u : V → ComplexBits B) (m : B)
    (a b : Expr V) (l : List (Expr V)) (e : ℚ)
    (hu : ∀ i, (u i).CutOn m) (ha : a.Safe u m) (hb : b.Safe u m)
    (hl : ∀ f ∈ l, f.Safe u m)
    (hLaw : ∀ (p : ℕ → B) (w : V → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
      (∀ n,p n ≤ m) → (∀ i, ComplexDecisionTrace p (u i) (w i)) →
      (∀ f ∈ l, ComplexDecisionTrace p (f.eval u) (f.evalGround w)) →
      dist (a.evalGround w) (b.evalGround w) ≤ (e : ℝ)) :
    m ≤ distanceLe (a.eval u) (b.eval u) e := by
  by_contra hF
  have haV := a.eval_cutOn u m hu ha
  have hbV := b.eval_cutOn u m hu hb
  obtain ⟨s,hs,hsm,hSep⟩ := cut_order_fail_survives (proper_distanceCut haV hbV) hF
  have huS : ∀ i, (u i).CutOn s := fun i =>
    ⟨properCutOn_mono hsm (hu i).1, properCutOn_mono hsm (hu i).2⟩
  have hL : ∀ f ∈ a :: b :: l, f.Safe u s := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact Expr.safe_mono ha hsm
    rcases List.mem_cons.mp hf with rfl|hf
    · exact Expr.safe_mono hb hsm
    · exact Expr.safe_mono (hl f hf) hsm
  obtain ⟨p,w,hp,hnz,hps,ht,hTr⟩ :=
    exists_expr_decision_completion u s hs huS (a :: b :: l) hL
  have hpm : ∀ n, p n ≤ m := fun n => (hps n).trans hsm
  have htA := hTr a List.mem_cons_self
  have htB := hTr b (List.mem_cons_of_mem _ List.mem_cons_self)
  have hAux : ∀ f ∈ l, ComplexDecisionTrace p (f.eval u) (f.evalGround w) :=
    fun f hf => hTr f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
  have hStrict := hSep hp hnz hps (trace_distanceCut hp hpm haV hbV htA htB)
    (checkedRealBits_traces p ((e : ℝ)^2))
  exact (not_le_of_gt hStrict)
    (pow_le_pow_left₀ dist_nonneg (hLaw p w hp hnz hpm ht hAux) 2)

end JSP000930.Negative
