import JSP000930AnalyticSentence
import JSP000933CheckedAddMulFactorial

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.PositiveForcing JSP000933.BooleanNames JSP000933.SetLanguage

private def naturalPowStep {d : ℕ} (p : Fin 1 → STerm d) (_ cur next : STerm d) :
    SForm d := multiplication_f cur (p 0) next

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_naturalPow_checked {n : ℕ} (v : DVec (V B) n)
    (a m r : STerm n) (x N y : ℕ)
    (ha : bTerm v a = bSet.of_nat x) (hm : bTerm v m = bSet.of_nat N)
    (hr : bTerm v r = bSet.of_nat y) :
    bTruth v (naturalPow_f a m r) = crispTruth B (y = x^N) := by
  let u (j : ℕ) := DVec.cons (bSet.of_nat j : V B) v
  let t : STerm (n+1) := bd_var ⟨0, Nat.succ_pos n⟩
  let S := fun (_ cur next : ℕ) => next = cur*x
  have hs (j : ℕ) : bTruth (u j) (successor_f zero t) = crispTruth B (j=1) :=
    bTruth_successor_twoChecked_r192 (u j) zero t 0 j
      (bTerm_zero_checked_r192 (u j)) (bTerm_current_r181 v (bSet.of_nat j))
  change bTruth v (exIn omega fun one =>
    bd_and (successor_f zero one)
      (naturalRecursion_f (up m) one (up r) (fun _ : Fin 1 => up a) naturalPowStep)) = _
  simp only [bTruth_exOmega_r192, boolean_realize_bounded_formula_and]
  change (⨆ j : ℕ, bTruth (u j) (successor_f zero t) ⊓
    bTruth (u j)
      (naturalRecursion_f (up m) t (up r) (fun _ : Fin 1 => up a) naturalPowStep)) = _
  simp only [hs, iSup_crispEquality_select_r193]
  have hStep : StepHasCheckedValue (B := B) (fun _ : Fin 1 => bTerm (u 1) (up a)) S
      naturalPowStep := by
    intro d w p i c r' I C R hp _ hc' hr'
    have hx : bTerm w (p 0) = bSet.of_nat x :=
      (hp 0).trans ((bTerm_up_r181 v (bSet.of_nat 1) a).trans ha)
    exact bTruth_multiplication_checked_r196 w c (p 0) r' C x R hc' hx hr'
  apply (bTruth_naturalRecursion_checked_r195 (u 1) (up m) t (up r) N 1 y
    ((bTerm_up_r181 v (bSet.of_nat 1) m).trans hm)
    (bTerm_current_r181 v (bSet.of_nat 1))
    ((bTerm_up_r181 v (bSet.of_nat 1) r).trans hr) _ S naturalPowStep hStep).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 N 1 y S (fun i => x^i)
  · exact pow_zero x
  · intro i _ z
    simp only [S, pow_succ]

end JSP000930.AnalyticSyntax
