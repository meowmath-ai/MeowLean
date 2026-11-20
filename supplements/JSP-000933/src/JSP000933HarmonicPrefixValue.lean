import JSP000933HarmonicStepValue

open Fol Lattice
open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def groundScaledHarmonic (allBits : Bool) (A C : Set ℕ) (p n : ℕ) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range n, if allBits=true ∨ j ∈ A \ C then Nat.factorial p/(j+1) else 0

theorem groundScaledHarmonic_zero_r199 (allBits : Bool) (A C : Set ℕ) (p : ℕ) :
    groundScaledHarmonic allBits A C p 0 = 0 := by
  classical
  simp [groundScaledHarmonic]

open scoped Classical in
theorem groundScaledHarmonic_succ_r199 (allBits : Bool) (A C : Set ℕ) (p n : ℕ) :
    groundScaledHarmonic allBits A C p (n+1) = groundScaledHarmonic allBits A C p n +
      (if allBits=true ∨ n ∈ A \ C then Nat.factorial p/(n+1) else 0) := by
  classical
  simp [groundScaledHarmonic,Finset.sum_range_succ]

theorem harmonicIncrement_factorial_iff_r199 {i n : ℕ} (hi : i < n) (cur next : ℕ) :
    HarmonicIncrement (Nat.factorial n) i cur next ↔ next = cur+Nat.factorial n/(i+1) := by
  have hpos : 0 < i+1 := Nat.succ_pos i
  constructor
  · rintro ⟨q,hq,hn⟩
    have he : Nat.factorial n/(i+1)=q := by rw [hq,Nat.mul_div_cancel_left q hpos]
    exact hn.trans (congrArg (fun q => cur+q) he.symm)
  · intro hn
    have hd : i+1 ∣ Nat.factorial n := Nat.dvd_factorial hpos (Nat.succ_le_of_lt hi)
    have hMul := Nat.div_mul_cancel hd
    exact ⟨Nat.factorial n/(i+1),(by simpa only [Nat.mul_comm] using hMul.symm),hn⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bTruth_harmonicPrefix_checked_r199 {n : ℕ} (v : DVec (V B) n)
    (allBits : Bool) (a b p r : STerm n) (A C : Set ℕ) (N R : ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (hp : bTerm v p = bSet.of_nat N) (hr : bTerm v r = bSet.of_nat R) :
    bTruth v (harmonicPrefixMass_f allBits a b p r) =
      crispTruth B (R = groundScaledHarmonic allBits A C N N) := by
  classical
  let u (fac : ℕ) := DVec.cons (bSet.of_nat fac) v
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let param (f : STerm (n+1)) (j : Fin 3) := if j=0 then up a else if j=1 then up b else f
  let S := fun (i cur next : ℕ) =>
    if allBits=true ∨ i ∈ A \ C then HarmonicIncrement (Nat.factorial N) i cur next else next=cur
  have hs (f : ℕ) : bTruth (u f) (factorial_f (up p) t) = crispTruth B (f=Nat.factorial N) :=
    bTruth_factorial_checked_r196 _ _ _ N f ((bTerm_up_r181 v _ p).trans hp) (bTerm_current_r181 v _)
  change bTruth v (exIn omega fun fac => bd_and (factorial_f (up p) fac)
    (naturalRecursion_f (up p) zero (up r) (param fac) (harmonicStep_f_r198 allBits))) = _
  simp only [bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ f : ℕ, bTruth (u f) (factorial_f (up p) t) ⊓
    bTruth (u f) (naturalRecursion_f (up p) zero (up r) (param t) (harmonicStep_f_r198 allBits))) = _
  simp only [hs,iSup_crispEquality_select_r193]
  have hParams :
      (fun j => bTerm (u (Nat.factorial N)) (param t j)) =
      (fun j : Fin 3 => if j=0 then groundSubsetName B A else
        if j=1 then groundSubsetName B C else bSet.of_nat (Nat.factorial N)) := by
    funext j
    dsimp only [param]
    by_cases h0 : j=0
    · simp only [ite_eq_left h0]
      exact (bTerm_up_r181 v (bSet.of_nat (Nat.factorial N)) a).trans ha
    · by_cases h1 : j=1
      · simp only [ite_eq_right h0,ite_eq_left h1]
        exact (bTerm_up_r181 v (bSet.of_nat (Nat.factorial N)) b).trans hb
      · simp only [ite_eq_right h0,ite_eq_right h1]
        exact bTerm_current_r181 v (bSet.of_nat (Nat.factorial N))
  have hS : StepHasCheckedValue (B := B) (fun j => bTerm (u (Nat.factorial N)) (param t j))
      S (harmonicStep_f_r198 allBits) := by
    rw [hParams]
    exact harmonicStep_checked_r198 allBits A C (Nat.factorial N)
  apply (bTruth_naturalRecursion_checked_r195 (u (Nat.factorial N)) (up p) zero (up r) N 0 R
    ((bTerm_up_r181 v _ p).trans hp) (bTerm_zero_checked_r192 _) ((bTerm_up_r181 v _ r).trans hr)
    (param t) S (harmonicStep_f_r198 allBits) hS).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 N 0 R S (groundScaledHarmonic allBits A C N)
  · exact groundScaledHarmonic_zero_r199 allBits A C N
  · intro i hi x
    rw [groundScaledHarmonic_succ_r199]
    by_cases h : allBits=true ∨ i ∈ A \ C
    · simpa only [S,ite_eq_left h] using
        harmonicIncrement_factorial_iff_r199 hi (groundScaledHarmonic allBits A C N i) x
    · simp only [S,ite_eq_right h,Nat.add_zero]

end SetLanguage
end JSP000933
