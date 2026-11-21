import JSP000930MixedFiniteExpressions

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.CantorCodes

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B]

def FixedMargins (u : V → ComplexBits B) (m : B) (l : List (Expr V)) : Prop :=
  ∀ d ∈ l, ∃ q : RatPresentation, 0 < q.value ∧ m ≤ (d.eval u).normSq q

theorem exists_fixedMargins (u : V → ComplexBits B) (l : List (Expr V))
    (m : B) (hm : m ≠ ⊥) (h : ∀ d ∈ l, m ≤ positiveCutValue (d.eval u).normSq) :
    ∃ r : B, r ≠ ⊥ ∧ r ≤ m ∧ FixedMargins u r l := by
  induction l generalizing m with
  | nil =>
    refine ⟨m,hm,le_rfl,?_⟩
    intro d hd
    exact (List.not_mem_nil hd).elim
  | cons a l ih =>
    have hA := h a List.mem_cons_self
    obtain ⟨q,s,hs,hsm,hsQ⟩ := exists_nonzero_below_choice_r135 m hm
      (fun q : {q : RatPresentation // 0 < q.value} => (a.eval u).normSq q.1) hA
    obtain ⟨r,hr,hrs,hrL⟩ := ih s hs (fun d hd =>
      hsm.trans (h d (List.mem_cons_of_mem _ hd)))
    refine ⟨r,hr,hrs.trans hsm,?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨q.1,q.2,hrs.trans hsQ⟩
    · exact hrL d hd

theorem Expr.trace_eval_of_fixedMargins {p : ℕ → B} (hp : Antitone p)
    (hnz : ∀ n,p n ≠ ⊥) {m : B} (hpm : ∀ n,p n ≤ m)
    {u : V → ComplexBits B} {u₀ : V → ℂ}
    (hu : ∀ i, (u i).CutOn m) (ht : ∀ i, ComplexDecisionTrace p (u i) (u₀ i))
    (e : Expr V) (hE : FixedMargins u m e.denominators) :
    ComplexDecisionTrace p (e.eval u) (e.evalGround u₀) := by
  have hSafe {a : Expr V} (hA : FixedMargins u m a.denominators) : a.Safe u m := by
    intro d hd
    obtain ⟨q,hq,hL⟩ := hA d hd
    exact hL.trans (le_iSup
      (fun r : {r : RatPresentation // 0 < r.value} => (d.eval u).normSq r.val) ⟨q,hq⟩)
  induction e with
  | atom i => exact ht i
  | num a b => exact checked_complex_traces p _
  | add a b ia ib =>
    have hA : FixedMargins u m a.denominators :=
      fun d hd => hE d (List.mem_append_left _ hd)
    have hB : FixedMargins u m b.denominators :=
      fun d hd => hE d (List.mem_append_right _ hd)
    exact (ia hA).add hp hpm (ib hB)
      (a.eval_cutOn u m hu (hSafe hA)) (b.eval_cutOn u m hu (hSafe hB))
  | mul a b ia ib =>
    have hA : FixedMargins u m a.denominators :=
      fun d hd => hE d (List.mem_append_left _ hd)
    have hB : FixedMargins u m b.denominators :=
      fun d hd => hE d (List.mem_append_right _ hd)
    exact (ia hA).mul hp hpm (ib hB)
      (a.eval_cutOn u m hu (hSafe hA)) (b.eval_cutOn u m hu (hSafe hB))
  | neg a ia =>
    exact (ia hE).neg hpm (a.eval_cutOn u m hu (hSafe hE))
  | inv a ia =>
    have hA : FixedMargins u m a.denominators := fun d hd =>
      hE d (List.mem_cons_of_mem _ hd)
    have ha := a.eval_cutOn u m hu (hSafe hA)
    obtain ⟨q,hq,hM⟩ := hE a List.mem_cons_self
    have htA := ia hA
    have hPos : m ≤ positiveCutValue (a.eval u).normSq := hM.trans (le_iSup
      (fun r : {r : RatPresentation // 0 < r.value} => (a.eval u).normSq r.val) ⟨q,hq⟩)
    have hX := trace_forcedMember_le hp hnz (htA.normSq hp hpm ha) q ⟨0,(hpm 0).trans hM⟩
    have hq' : (0 : ℝ) < (q.value : ℝ) := by exact_mod_cast hq
    exact ComplexDecisionTrace.inv_of_positive hp hpm ha htA hPos (hq'.trans_le hX)

end JSP000930.Negative
