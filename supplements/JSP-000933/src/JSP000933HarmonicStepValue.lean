import JSP000933OrdinaryPrefixValue

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def HarmonicIncrement (fac i cur next : ℕ) : Prop :=
  ∃ q : ℕ, fac = (i+1)*q ∧ next = cur+q

def harmonicIncrement_f_r198 {n : ℕ} (fac i cur next : STerm n) : SForm n :=
  exIn omega fun d =>
    exIn omega fun q =>
      bd_and (successor_f (up2 i) (up d))
        (bd_and (multiplication_f (up d) q (up2 fac)) (addition_f (up2 cur) q (up2 next)))

theorem bTruth_harmonicIncrement_checked_r198 {n : ℕ} (v : DVec (V B) n)
    (fac i cur next : STerm n) (F I C N : ℕ)
    (hf : bTerm v fac = bSet.of_nat F) (hi : bTerm v i = bSet.of_nat I)
    (hc : bTerm v cur = bSet.of_nat C) (hn : bTerm v next = bSet.of_nat N) :
    bTruth v (harmonicIncrement_f_r198 fac i cur next) = crispTruth B (HarmonicIncrement F I C N) := by
  let dt : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let qt : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let u (d q : ℕ) := DVec.cons (bSet.of_nat q) (DVec.cons (bSet.of_nat d) v)
  have hD (d q : ℕ) : bTerm (u d q) (up dt) = bSet.of_nat d := by
    exact (bTerm_up_r181 (DVec.cons (bSet.of_nat d) v) (bSet.of_nat q) dt).trans
      (bTerm_current_r181 v (bSet.of_nat d))
  have hQ (d q : ℕ) : bTerm (u d q) qt = bSet.of_nat q :=
    bTerm_current_r181 _ _
  have hs (d q : ℕ) :
      bTruth (u d q) (successor_f (up2 i) (up dt)) = crispTruth B (d=I+1) :=
    bTruth_successor_twoChecked_r192 _ _ _ I d ((bTerm_up2_r181 v _ _ i).trans hi) (hD d q)
  have hm (d q : ℕ) :
      bTruth (u d q) (multiplication_f (up dt) qt (up2 fac)) = crispTruth B (F=d*q) :=
    bTruth_multiplication_checked_r196 _ _ _ _ d q F (hD d q) (hQ d q)
      ((bTerm_up2_r181 v _ _ fac).trans hf)
  have ha (d q : ℕ) :
      bTruth (u d q) (addition_f (up2 cur) qt (up2 next)) = crispTruth B (N=C+q) :=
    bTruth_addition_checked_r196 _ _ _ _ C q N ((bTerm_up2_r181 v _ _ cur).trans hc)
      (hQ d q) ((bTerm_up2_r181 v _ _ next).trans hn)
  simp only [harmonicIncrement_f_r198,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  have hEval (d q : ℕ) : bTruth (u d q) (successor_f (up2 i) (up dt)) ⊓
      (bTruth (u d q) (multiplication_f (up dt) qt (up2 fac)) ⊓
        bTruth (u d q) (addition_f (up2 cur) qt (up2 next))) =
      crispTruth B (d=I+1) ⊓ (crispTruth B (F=d*q) ⊓ crispTruth B (N=C+q)) := by
    rw [hs,hm,ha]
  change (⨆ d : ℕ, ⨆ q : ℕ, bTruth (u d q) (successor_f (up2 i) (up dt)) ⊓
    (bTruth (u d q) (multiplication_f (up dt) qt (up2 fac)) ⊓
      bTruth (u d q) (addition_f (up2 cur) qt (up2 next)))) = _
  simp only [hEval]
  simp only [← crisp_and_r190,iSup_crisp_r192,HarmonicIncrement]
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨d,q,rfl,hMul,hAdd⟩
    exact ⟨q,hMul,hAdd⟩
  · rintro ⟨q,hMul,hAdd⟩
    exact ⟨I+1,q,rfl,hMul,hAdd⟩

def harmonicStep_f_r198 {d : ℕ} (allBits : Bool)
    (p : Fin 3 → STerm d) (i cur next : STerm d) : SForm d :=
  let b := if allBits then bd_not bd_falsum else differenceBit_f (p 0) (p 1) i
  bd_and (bd_imp b (harmonicIncrement_f_r198 (p 2) i cur next))
    (bd_imp (bd_not b) (bd_equal cur next))

open scoped Classical in
theorem harmonicStep_checked_r198 (allBits : Bool) (A C : Set ℕ) (F : ℕ) :
    StepHasCheckedValue (B := B)
      (fun j : Fin 3 => if j=0 then groundSubsetName B A else if j=1 then groundSubsetName B C else bSet.of_nat F)
      (fun i cur next => if allBits = true ∨ i ∈ A \ C then HarmonicIncrement F i cur next else next=cur)
      (harmonicStep_f_r198 allBits) := by
  classical
  intro d v p i cur next I Y Z hP hi hc hn
  have hp0 : bTerm v (p 0) = groundSubsetName B A := by simpa using hP 0
  have hp1 : bTerm v (p 1) = groundSubsetName B C := by simpa using hP 1
  have hp2 : bTerm v (p 2) = bSet.of_nat F := by simpa using hP 2
  let b : SForm d := if allBits then bd_not bd_falsum else differenceBit_f (p 0) (p 1) i
  have hBit : bTruth v b = crispTruth B (allBits=true ∨ I ∈ A \ C) := by
    cases allBits
    · simpa [b] using bTruth_differenceBit_checked_r197 v (p 0) (p 1) i A C I hp0 hp1 hi
    · simp [b,crispTruth,boolean_realize_bounded_formula_not,boolean_realize_bounded_formula]
  have hIncrement := bTruth_harmonicIncrement_checked_r198 v (p 2) i cur next F I Y Z hp2 hi hc hn
  change bTruth v (bd_and (bd_imp b (harmonicIncrement_f_r198 (p 2) i cur next))
    (bd_imp (bd_not b) (bd_equal cur next))) = _
  simp only [boolean_realize_bounded_formula_and,bTruth_imp_r181,boolean_realize_bounded_formula_not,
    hBit,hIncrement,bTruth_equal_r181,hc,hn,checkedNat_eq_crisp_r189]
  rw [← crisp_not_r197,← crisp_imp_r190,← crisp_imp_r190,← crisp_and_r190]
  apply crispTruth_propext_r188
  by_cases h : allBits=true ∨ I ∈ A \ C
  · simp only [h, true_implies, not_true_eq_false, false_implies, and_true, ite_true]
  · simp only [h, false_implies, not_false_eq_true, true_implies, true_and, ite_false, eq_comm]

end SetLanguage
end JSP000933
