import JSP000933MixedFirstOrderRecursion
import JSP000933HarmonicPrefixValue

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def mixedDiffBit (A C : bSet B) (i : ℕ) : B :=
  membershipBits A i ⊓ (membershipBits C i)ᶜ

def mixedHarmonicBit (allBits : Bool) (A C : bSet B) (i : ℕ) : B :=
  if allBits then ⊤ else mixedDiffBit A C i

noncomputable def mixedOrdinaryStep (A C : bSet B) (i cur next : ℕ) : B :=
  imp (mixedDiffBit A C i) (crispTruth B (next=cur+1)) ⊓
    imp (mixedDiffBit A C i)ᶜ (crispTruth B (cur=next))

noncomputable def mixedHarmonicStep (allBits : Bool) (A C : bSet B) (F i cur next : ℕ) : B :=
  imp (mixedHarmonicBit allBits A C i) (crispTruth B (HarmonicIncrement F i cur next)) ⊓
    imp (mixedHarmonicBit allBits A C i)ᶜ (crispTruth B (cur=next))

theorem bTruth_mixedDiffBit_r210 {n : ℕ} (v : DVec (V B) n) (a b t : STerm n)
    (i : ℕ) (ht : bTerm v t = bSet.of_nat i) :
    bTruth v (differenceBit_f a b t) = mixedDiffBit (bTerm v a) (bTerm v b) i := by
  simp only [differenceBit_f,boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_not,
    boolean_realize_bounded_formula_mem',ht,mixedDiffBit,membershipBits]

def mixedOrdinaryStep_f {d : ℕ} (p : Fin 2 → STerm d) (i cur next : STerm d) : SForm d :=
  let b := differenceBit_f (p 0) (p 1) i
  bd_and (bd_imp b (successor_f cur next)) (bd_imp (bd_not b) (bd_equal cur next))

theorem mixedOrdinaryStep_computes_r210 (A C : bSet B) :
    StepHasBooleanValue (B := B) (fun j : Fin 2 => if j=0 then A else C)
      (mixedOrdinaryStep A C) mixedOrdinaryStep_f := by
  intro d v p i cur next I Y Z hP hi hc hn
  have h0 : bTerm v (p 0) = A := by simpa using hP 0
  have h1 : bTerm v (p 1) = C := by simpa using hP 1
  have hBit := bTruth_mixedDiffBit_r210 v (p 0) (p 1) i I hi
  rw [h0,h1] at hBit
  have hSucc := bTruth_successor_twoChecked_r192 v cur next Y Z hc hn
  simp only [mixedOrdinaryStep_f,mixedOrdinaryStep,boolean_realize_bounded_formula_and,
    bTruth_imp_r181,boolean_realize_bounded_formula_not,hBit,hSucc,
    bTruth_equal_r181,hc,hn,checkedNat_eq_crisp_r189]

theorem mixedHarmonicStep_computes_r210 (allBits : Bool) (A C : bSet B) (F : ℕ) :
    StepHasBooleanValue (B := B)
      (fun j : Fin 3 => if j=0 then A else if j=1 then C else bSet.of_nat F)
      (mixedHarmonicStep allBits A C F) (harmonicStep_f_r198 allBits) := by
  intro d v p i cur next I Y Z hP hi hc hn
  have h0 : bTerm v (p 0) = A := by simpa using hP 0
  have h1 : bTerm v (p 1) = C := by simpa using hP 1
  have h2 : bTerm v (p 2) = bSet.of_nat F := by simpa using hP 2
  let bit : SForm d := if allBits then bd_not bd_falsum else differenceBit_f (p 0) (p 1) i
  have hBit : bTruth v bit = mixedHarmonicBit allBits A C I := by
    cases allBits
    · simpa [bit,mixedHarmonicBit,h0,h1] using bTruth_mixedDiffBit_r210 v (p 0) (p 1) i I hi
    · simp [bit,mixedHarmonicBit,boolean_realize_bounded_formula_not,boolean_realize_bounded_formula]
  have hInc := bTruth_harmonicIncrement_checked_r198 v (p 2) i cur next F I Y Z h2 hi hc hn
  change bTruth v (bd_and (bd_imp bit (harmonicIncrement_f_r198 (p 2) i cur next))
    (bd_imp (bd_not bit) (bd_equal cur next))) = _
  simp only [mixedHarmonicStep,boolean_realize_bounded_formula_and,bTruth_imp_r181,
    boolean_realize_bounded_formula_not,hBit,hInc,bTruth_equal_r181,hc,hn,checkedNat_eq_crisp_r189]

theorem bTruth_mixedOrdinaryPrefix_r210 {n : ℕ} (v : DVec (V B) n)
    (a b p r : STerm n) (N R : ℕ)
    (hp : bTerm v p = bSet.of_nat N) (hr : bTerm v r = bSet.of_nat R) :
    bTruth v (ordinaryPrefixCount_f a b p r) =
      recurrenceOfTables B N 0 R (mixedOrdinaryStep (bTerm v a) (bTerm v b)) := by
  let param := fun j : Fin 2 => if j=0 then a else b
  have hP : (fun j => bTerm v (param j)) =
      (fun j : Fin 2 => if j=0 then bTerm v a else bTerm v b) := by
    funext j
    by_cases h : j=0 <;> simp [param,h]
  have hS : StepHasBooleanValue (B := B) (fun j => bTerm v (param j))
      (mixedOrdinaryStep (bTerm v a) (bTerm v b)) mixedOrdinaryStep_f := by
    rw [hP]
    exact mixedOrdinaryStep_computes_r210 _ _
  change bTruth v (naturalRecursion_f p zero r param mixedOrdinaryStep_f) = _
  exact bTruth_naturalRecursion_value_r209 v p zero r N 0 R hp (bTerm_zero_checked_r192 v)
    hr param _ mixedOrdinaryStep_f hS

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bTruth_mixedHarmonicPrefix_r210 {n : ℕ} (v : DVec (V B) n)
    (allBits : Bool) (a b p r : STerm n) (N R : ℕ)
    (hp : bTerm v p = bSet.of_nat N) (hr : bTerm v r = bSet.of_nat R) :
    bTruth v (harmonicPrefixMass_f allBits a b p r) =
      recurrenceOfTables B N 0 R (mixedHarmonicStep allBits (bTerm v a) (bTerm v b) (Nat.factorial N)) := by
  let u (fac : ℕ) := DVec.cons (bSet.of_nat fac) v
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let param (f : STerm (n+1)) (j : Fin 3) := if j=0 then up a else if j=1 then up b else f
  let A := bTerm v a
  let C := bTerm v b
  have hs (f : ℕ) : bTruth (u f) (factorial_f (up p) t) = crispTruth B (f=Nat.factorial N) :=
    bTruth_factorial_checked_r196 _ _ _ N f ((bTerm_up_r181 v _ p).trans hp) (bTerm_current_r181 v _)
  change bTruth v (exIn omega fun fac => bd_and (factorial_f (up p) fac)
    (naturalRecursion_f (up p) zero (up r) (param fac) (harmonicStep_f_r198 allBits))) = _
  simp only [bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ f : ℕ, bTruth (u f) (factorial_f (up p) t) ⊓
    bTruth (u f) (naturalRecursion_f (up p) zero (up r) (param t) (harmonicStep_f_r198 allBits))) = _
  simp only [hs,iSup_crispEquality_select_r193]
  have hP : (fun j => bTerm (u (Nat.factorial N)) (param t j)) =
      (fun j : Fin 3 => if j=0 then A else if j=1 then C else bSet.of_nat (Nat.factorial N)) := by
    funext j
    dsimp only [param]
    by_cases h0 : j=0
    · simp only [ite_eq_left h0]
      exact bTerm_up_r181 v (bSet.of_nat (Nat.factorial N)) a
    · by_cases h1 : j=1
      · simp only [ite_eq_right h0,ite_eq_left h1]
        exact bTerm_up_r181 v (bSet.of_nat (Nat.factorial N)) b
      · simp only [ite_eq_right h0,ite_eq_right h1]
        exact bTerm_current_r181 v (bSet.of_nat (Nat.factorial N))
  have hS : StepHasBooleanValue (B := B) (fun j => bTerm (u (Nat.factorial N)) (param t j))
      (mixedHarmonicStep allBits A C (Nat.factorial N)) (harmonicStep_f_r198 allBits) := by
    rw [hP]
    exact mixedHarmonicStep_computes_r210 allBits A C (Nat.factorial N)
  exact bTruth_naturalRecursion_value_r209 (u (Nat.factorial N)) (up p) zero (up r) N 0 R
    ((bTerm_up_r181 v _ p).trans hp) (bTerm_zero_checked_r192 _) ((bTerm_up_r181 v _ r).trans hr)
    (param t) _ (harmonicStep_f_r198 allBits) hS

end SetLanguage
end JSP000933
