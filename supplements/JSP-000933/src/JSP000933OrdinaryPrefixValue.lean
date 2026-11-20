import JSP000933CheckedAddMulFactorial

open Fol Lattice
open scoped Flypitch BigOperators

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem crisp_not_r197 (P : Prop) :
    crispTruth B (¬ P) = (crispTruth B P)ᶜ := by
  classical
  by_cases h : P <;> simp [crispTruth,h]

theorem checkedNat_ground_mem_r197 (A : Set ℕ) (i : ℕ) :
    ((bSet.of_nat i : bSet B) ∈ᴮ groundSubsetName B A) = crispTruth B (i ∈ A) := by
  change membershipBits (realBitsName (groundSubsetBits B A)) i = _
  have h := congrFun (membershipBits_realBitsName_r128 (groundSubsetBits B A)) i
  exact h.trans rfl

theorem bTruth_differenceBit_checked_r197 {n : ℕ} (v : DVec (V B) n)
    (a b i : STerm n) (A C : Set ℕ) (I : ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (hi : bTerm v i = bSet.of_nat I) :
    bTruth v (differenceBit_f a b i) = crispTruth B (I ∈ A \ C) := by
  simp only [differenceBit_f,boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_not,
    boolean_realize_bounded_formula_mem',ha,hb,hi,checkedNat_ground_mem_r197]
  rw [← crisp_not_r197,← crisp_and_r190] <;> rfl

noncomputable def groundCount (A C : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range n, if j ∈ A \ C then 1 else 0

theorem groundCount_zero_r197 (A C : Set ℕ) : groundCount A C 0 = 0 := by
  classical
  simp [groundCount]

open scoped Classical in
theorem groundCount_step_r197 (A C : Set ℕ) (n : ℕ) :
    groundCount A C (n+1) = groundCount A C n + (if n ∈ A \ C then 1 else 0) := by
  classical
  unfold groundCount
  rw [Finset.sum_range_succ]

private def ordinaryStep_r197 {d : ℕ} (p : Fin 2 → STerm d) (i cur next : STerm d) : SForm d :=
  let b := differenceBit_f (p 0) (p 1) i
  bd_and (bd_imp b (successor_f cur next)) (bd_imp (bd_not b) (bd_equal cur next))

open scoped Classical in
private theorem ordinaryStep_checked_r197 (A C : Set ℕ) :
    StepHasCheckedValue (B := B) (fun j : Fin 2 => if j = 0 then groundSubsetName B A else groundSubsetName B C)
      (fun i cur next => if i ∈ A \ C then next=cur+1 else next=cur) ordinaryStep_r197 := by
  classical
  intro d v params i c r I Y Z hParams hi hc hr
  have hp0 : bTerm v (params 0) = groundSubsetName B A := by simpa using hParams 0
  have hp1 : bTerm v (params 1) = groundSubsetName B C := by simpa using hParams 1
  have hBit := bTruth_differenceBit_checked_r197 v (params 0) (params 1) i A C I hp0 hp1 hi
  have hSucc := bTruth_successor_twoChecked_r192 v c r Y Z hc hr
  simp only [ordinaryStep_r197,boolean_realize_bounded_formula_and,bTruth_imp_r181,
    boolean_realize_bounded_formula_not,bTruth_equal_r181,hBit,hSucc,hc,hr,checkedNat_eq_crisp_r189]
  rw [← crisp_not_r197,← crisp_imp_r190,← crisp_imp_r190,← crisp_and_r190]
  apply crispTruth_propext_r188
  by_cases h : I ∈ A \ C
  · simp [h]
  · simp [h,eq_comm]

theorem bTruth_ordinaryPrefix_checked_r197 {n : ℕ} (v : DVec (V B) n)
    (a b p r : STerm n) (A C : Set ℕ) (N R : ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (hp : bTerm v p = bSet.of_nat N) (hr : bTerm v r = bSet.of_nat R) :
    bTruth v (ordinaryPrefixCount_f a b p r) = crispTruth B (R = groundCount A C N) := by
  classical
  let S := fun (i cur next : ℕ) => if i ∈ A \ C then next = cur+1 else next = cur
  let param := fun j : Fin 2 => if j = 0 then a else b
  have hP : StepHasCheckedValue (B := B) (fun j => bTerm v (param j)) S ordinaryStep_r197 := by
    have h : (fun j => bTerm v (param j)) =
        (fun j : Fin 2 => if j = 0 then groundSubsetName B A else groundSubsetName B C) := by
      funext j
      by_cases he : j = 0 <;> simp [param,he,ha,hb]
    rw [h]
    intro d w params it yt zt i y z hParams hi hy hz
    exact ordinaryStep_checked_r197 (B := B) A C (d := d) w params it yt zt i y z hParams hi hy hz
  change bTruth v (naturalRecursion_f p zero r param ordinaryStep_r197) = _
  apply (bTruth_naturalRecursion_checked_r195 v p zero r N 0 R hp (bTerm_zero_checked_r192 v)
    hr param S ordinaryStep_r197 hP).trans
  apply crispTruth_propext_r188
  apply finiteRecursion_deterministic_r196 N 0 R S (groundCount A C)
  · exact groundCount_zero_r197 A C
  · intro i hi t
    rw [groundCount_step_r197]
    by_cases he : i ∈ A \ C
    · simp only [S,ite_eq_left he]
    · simp only [S,ite_eq_right he,Nat.add_zero]

end SetLanguage
end JSP000933
