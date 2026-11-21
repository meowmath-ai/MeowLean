import JSP000930AnalyticRadiusBudget

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem inf_iInf_nat (p : B) (F : ℕ → B) :
    p ⊓ (⨅ n : ℕ, F n) = ⨅ n : ℕ, p ⊓ F n := by
  apply le_antisymm
  · exact le_iInf fun n => inf_le_inf_left _ (iInf_le _ n)
  · exact le_inf ((iInf_le _ 0).trans inf_le_left)
      (le_iInf fun n => (iInf_le _ n).trans inf_le_right)

theorem bTruth_radiusAt_masked {n : ℕ} (v : DVec (V B) n) (A R : STerm n)
    (r : ℕ) (p : B) (hR : bTerm v R = bSet.of_nat r)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hA : ∀ i, (sequenceBits (bTerm v A) i).CutOn p)
    (hVal : ∀ i, p ≤ bSet.pair (bSet.of_nat i) (sequenceBits (bTerm v A) i).name ∈ᴮ bTerm v A) :
    p ⊓ bTruth v (radiusAt_f A R) =
      p ⊓ (⨆ k : ℕ, ⨅ i : ℕ, radiusBudgetBits (sequenceBits (bTerm v A) i) r k i) := by
  simp only [radiusAt_f,bTruth_exOmega_r192,bTruth_allOmega_r192]
  rw [inf_iSup_eq,inf_iSup_eq]
  apply iSup_congr
  intro k
  rw [inf_iInf_nat,inf_iInf_nat]
  apply iInf_congr
  intro i
  let v1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) k) v
  let v2 : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) i) v1
  let K : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let I : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let z := sequenceBits (bTerm v A) i
  change p ⊓ bTruth v2 (radiusBudget_f (up2 A) (up2 R) (up K) I) = p ⊓ radiusBudgetBits z r k i
  have hA' : bTerm v2 (up2 A) = bTerm v A :=
    bTerm_up2_r181 v (bSet.of_nat k) (bSet.of_nat i) A
  exact bTruth_radiusBudget_weighted v2 (up2 A) (up2 R) (up K) I z r k i p
    ((bTerm_up2_r181 v (bSet.of_nat k) (bSet.of_nat i) R).trans hR)
    ((bTerm_up_r181 v1 (bSet.of_nat i) K).trans (bTerm_current_r181 v (bSet.of_nat k)))
    (bTerm_current_r181 v1 (bSet.of_nat i)) (hA i)
    (by rw [hA']; exact hF) (by rw [hA']; exact hVal i)

theorem forces_entireRadii_iff {n : ℕ} (v : DVec (V B) n) (A : STerm n) (p : B)
    (hSeq : p ≤ bTruth v (sequence_f A)) :
    p ≤ bTruth v (entireRadii_f A) ↔ GrowthOn p (sequenceBits (bTerm v A)) := by
  obtain ⟨hf,ha,hval⟩ := sequenceBits_actual v A p hSeq
  let V (r : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) r) v
  let R0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hMask (r : ℕ) : p ⊓ bTruth (V r) (radiusAt_f (up A) R0) =
      p ⊓ (⨆ k : ℕ, ⨅ i : ℕ, radiusBudgetBits (sequenceBits (bTerm v A) i) r k i) := by
    have he : bTerm (V r) (up A) = bTerm v A := bTerm_up_r181 v (bSet.of_nat r) A
    simpa only [he] using bTruth_radiusAt_masked (V r) (up A) R0 r p
      (bTerm_current_r181 v (bSet.of_nat r))
      (by rw [he]; exact hf) (by rw [he]; exact ha) (by rw [he]; exact hval)
  have hguard (r : ℕ) : bTruth (V r) (bd_not (bd_equal R0 zero)) =
      (crispTruth B (r=0))ᶜ := by
    have h : bTruth (V r) (bd_not (bd_equal R0 zero)) =
        (bTruth (V r) (bd_equal R0 zero))ᶜ := boolean_realize_bounded_formula_not
    rw [h,bTruth_equal_r181,bTerm_current_r181 v (bSet.of_nat r),
      bTerm_zero_checked_r192,checkedNat_eq_crisp_r189]
  rw [entireRadii_f,bTruth_allOmega_r192]
  constructor
  · intro h
    intro r hr
    have hR := h.trans (iInf_le _ r)
    change p ≤ bTruth (V r) (bd_imp (bd_not (bd_equal R0 zero)) (radiusAt_f (up A) R0)) at hR
    rw [bTruth_imp_r181,hguard] at hR
    have hn : r ≠ 0 := by omega
    simp only [crispTruth,hn,ite_false,compl_bot] at hR
    rw [← _root_.deduction,inf_top_eq] at hR
    exact (le_inf le_rfl hR).trans ((hMask r).le.trans inf_le_right)
  · intro h
    refine le_iInf fun r => ?_
    change p ≤ bTruth (V r) (bd_imp (bd_not (bd_equal R0 zero)) (radiusAt_f (up A) R0))
    rw [bTruth_imp_r181,hguard,← _root_.deduction]
    by_cases hr : r = 0
    · simp [crispTruth,hr]
    · simp only [crispTruth,hr,ite_false,compl_bot,inf_top_eq]
      exact (le_inf le_rfl (h r (by omega))).trans ((hMask r).symm.le.trans inf_le_right)

theorem entire_growthOn {n : ℕ} (v : DVec (V B) n) (A : STerm n) (p : B)
    (hA : p ≤ bTruth v (isEntireCode_f A)) :
    GrowthOn p (sequenceBits (bTerm v A)) := by
  simp only [isEntireCode_f,bTruth_and_eq] at hA
  exact (forces_entireRadii_iff v A p (hA.trans inf_le_left)).1 (hA.trans inf_le_right)

end JSP000930.AnalyticSyntax
