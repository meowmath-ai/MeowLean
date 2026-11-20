import JSP000933FirstOrderFiniteRecursion
import Mathlib.Data.Nat.Factorial.Basic

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem finiteRecursion_deterministic_r196 (n base out : ℕ) (Step : ℕ → ℕ → ℕ → Prop)
    (v : ℕ → ℕ) (h0 : v 0 = base)
    (hs : ∀ i < n, ∀ x, Step i (v i) x ↔ x = v (i+1)) :
    FiniteRecursion n base out Step ↔ out = v n := by
  constructor
  · rintro ⟨f,hf0,hfN,hfS⟩
    have hh : ∀ i : ℕ, ∀ hi : i < n+1, f ⟨i,hi⟩ = v i := by
      intro i
      induction i with
      | zero => intro hi; exact hf0.trans h0.symm
      | succ i ih =>
        intro hi
        have hin : i < n := Nat.lt_of_succ_lt_succ hi
        have h := hfS (⟨i,hin⟩ : Fin n)
        change Step i (f ⟨i,hin.trans_le (Nat.le_succ n)⟩) (f ⟨i+1,hi⟩) at h
        rw [ih (hin.trans_le (Nat.le_succ n))] at h
        exact (hs i hin _).mp h
    exact hfN.symm.trans (hh n (Nat.lt_succ_self n))
  · intro h
    refine ⟨fun i => v i.val,h0, h.symm,?_⟩
    intro i
    exact (hs i.val i.isLt _).mpr rfl

theorem bTruth_addition_checked_r196 {n : ℕ} (v : DVec (V B) n) (a b c : STerm n)
    (x y z : ℕ) (ha : bTerm v a = bSet.of_nat x) (hb : bTerm v b = bSet.of_nat y)
    (hc : bTerm v c = bSet.of_nat z) :
    bTruth v (addition_f a b c) = crispTruth B (z = x+y) := by
  let S := fun (_ cur next : ℕ) => next = cur+1
  let step : ∀ {d : ℕ}, (Fin 0 → STerm d) → STerm d → STerm d → STerm d → SForm d :=
    fun _ _ cur next => successor_f cur next
  have hStep : StepHasCheckedValue (B := B) (fun i : Fin 0 => bTerm v (Fin.elim0 i)) S step := by
    intro d w p i a c I A C hp hi ha hc
    exact bTruth_successor_twoChecked_r192 w a c A C ha hc
  change bTruth v (naturalRecursion_f b a c (fun i : Fin 0 => Fin.elim0 i) step) = _
  apply (bTruth_naturalRecursion_checked_r195 v b a c y x z hb ha hc _ S step hStep).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 y x z S (fun i => x+i)
  · exact Nat.add_zero x
  · intro i hi t
    simp only [S,Nat.add_assoc]

theorem bTruth_multiplication_checked_r196 {n : ℕ} (v : DVec (V B) n) (a b c : STerm n)
    (x y z : ℕ) (ha : bTerm v a = bSet.of_nat x) (hb : bTerm v b = bSet.of_nat y)
    (hc : bTerm v c = bSet.of_nat z) :
    bTruth v (multiplication_f a b c) = crispTruth B (z = x*y) := by
  let S := fun (_ cur next : ℕ) => next = cur+x
  let step : ∀ {d : ℕ}, (Fin 1 → STerm d) → STerm d → STerm d → STerm d → SForm d :=
    fun p _ cur next => addition_f cur (p 0) next
  have hStep : StepHasCheckedValue (B := B) (fun _ : Fin 1 => bTerm v a) S step := by
    intro d w p i a' c' I A C hp hi ha' hc'
    exact bTruth_addition_checked_r196 w a' (p 0) c' A x C ha' ((hp 0).trans ha) hc'
  change bTruth v (naturalRecursion_f b zero c (fun _ : Fin 1 => a) step) = _
  apply (bTruth_naturalRecursion_checked_r195 v b zero c y 0 z hb
    (bTerm_zero_checked_r192 v) hc _ S step hStep).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 y 0 z S (fun i => x*i)
  · exact Nat.mul_zero x
  · intro i hi t
    simp only [S,Nat.mul_succ]

private def factorialStep_r196 {d : ℕ} (_ : Fin 0 → STerm d) (i cur next : STerm d) : SForm d :=
  exIn omega fun j => bd_and (successor_f (up i) j) (multiplication_f (up cur) j (up next))

theorem factorialStep_checked_r196 {d : ℕ} (v : DVec (V B) d)
    (p : Fin 0 → STerm d) (i cur next : STerm d) (I C N : ℕ)
    (hi : bTerm v i = bSet.of_nat I) (hc : bTerm v cur = bSet.of_nat C)
    (hn : bTerm v next = bSet.of_nat N) :
    bTruth v (factorialStep_r196 p i cur next) = crispTruth B (N = C*(I+1)) := by
  have hs (j : ℕ) :
      bTruth (DVec.cons (bSet.of_nat j) v) (successor_f (up i) (bd_var ⟨0,Nat.succ_pos d⟩)) =
      crispTruth B (j=I+1) :=
    bTruth_successor_twoChecked_r192 _ _ _ I j ((bTerm_up_r181 v _ i).trans hi) (bTerm_current_r181 v _)
  have hm (j : ℕ) :
      bTruth (DVec.cons (bSet.of_nat j) v)
        (multiplication_f (up cur) (bd_var ⟨0,Nat.succ_pos d⟩) (up next)) =
      crispTruth B (N=C*j) :=
    bTruth_multiplication_checked_r196 _ _ _ _ C j N ((bTerm_up_r181 v _ cur).trans hc)
      (bTerm_current_r181 v _) ((bTerm_up_r181 v _ next).trans hn)
  simp only [factorialStep_r196,bTruth_exOmega_r192,boolean_realize_bounded_formula_and,hs,hm,
    iSup_crispEquality_select_r193]

theorem bTruth_factorial_checked_r196 {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (x y : ℕ) (ha : bTerm v a = bSet.of_nat x) (hb : bTerm v b = bSet.of_nat y) :
    bTruth v (factorial_f a b) = crispTruth B (y = Nat.factorial x) := by
  let u (j : ℕ) := DVec.cons (bSet.of_nat j) v
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let S := fun (i cur next : ℕ) => next = cur*(i+1)
  have hs (j : ℕ) : bTruth (u j) (successor_f zero t) = crispTruth B (j=1) :=
    bTruth_successor_twoChecked_r192 _ _ _ 0 j (bTerm_zero_checked_r192 _) (bTerm_current_r181 v _)
  change bTruth v (exIn omega fun one =>
    bd_and (successor_f zero one)
      (naturalRecursion_f (up a) one (up b) (fun i : Fin 0 => Fin.elim0 i) factorialStep_r196)) = _
  simp only [bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ j : ℕ, bTruth (u j) (successor_f zero t) ⊓
    bTruth (u j) (naturalRecursion_f (up a) t (up b) (fun i : Fin 0 => Fin.elim0 i) factorialStep_r196)) = _
  simp only [hs,iSup_crispEquality_select_r193]
  have hStep : StepHasCheckedValue (B := B) (fun i : Fin 0 => bTerm (u 1) (Fin.elim0 i)) S factorialStep_r196 := by
    intro d w p i c r I C R hp hi hc hr
    exact factorialStep_checked_r196 w p i c r I C R hi hc hr
  apply (bTruth_naturalRecursion_checked_r195 (u 1) (up a) t (up b) x 1 y
    ((bTerm_up_r181 v _ a).trans ha) (bTerm_current_r181 v _) ((bTerm_up_r181 v _ b).trans hb)
    _ S factorialStep_r196 hStep).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 x 1 y S Nat.factorial
  · rfl
  · intro i hi t
    simp only [S,Nat.factorial_succ,Nat.mul_comm]

end SetLanguage
end JSP000933
