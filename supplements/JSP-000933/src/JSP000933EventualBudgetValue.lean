import JSP000933IntegerBudgetValue

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def EventuallyIntegerBudget (P : ℕ → ℕ → Prop) : Prop :=
  ∀ k : ℕ, k ≠ 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P k n

def OrdinaryIntegerNull (A C : Set ℕ) : Prop :=
  EventuallyIntegerBudget (fun k n => k * groundCount A C n ≤ n)

def HarmonicIntegerNull (A C : Set ℕ) : Prop :=
  EventuallyIntegerBudget
    (fun k n => k * groundScaledHarmonic false A C n n ≤ groundScaledHarmonic true A C n n)

theorem bTruth_eventualBudget_checked_r201 {n : ℕ} (v : DVec (V B) n)
    (a b : STerm n) (A C : Set ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (budget : ∀ {d : ℕ}, STerm d → STerm d → STerm d → STerm d → SForm d)
    (P : ℕ → ℕ → Prop)
    (hBudget : ∀ {d : ℕ} (u : DVec (V B) d) (aTerm bTerm' kt pt : STerm d) (k p : ℕ),
      bTerm u aTerm = groundSubsetName B A → bTerm u bTerm' = groundSubsetName B C →
      bTerm u kt = bSet.of_nat k → bTerm u pt = bSet.of_nat p →
      bTruth u (budget aTerm bTerm' kt pt) = crispTruth B (P k p)) :
    bTruth v (eventualBudget_f a b budget) = crispTruth B (EventuallyIntegerBudget P) := by
  let kt : STerm (n+1) := bd_var ⟨0,by omega⟩
  let nt : STerm (n+2) := bd_var ⟨0,by omega⟩
  let pt : STerm (n+3) := bd_var ⟨0,by omega⟩
  let u (k N p : ℕ) := DVec.cons (bSet.of_nat p) (DVec.cons (bSet.of_nat N) (DVec.cons (bSet.of_nat k) v))
  have hNE (k : ℕ) :
      bTruth (DVec.cons (bSet.of_nat k) v) (bd_not (bd_equal kt zero)) = crispTruth B (k ≠ 0) := by
    have hEq : bTruth (DVec.cons (bSet.of_nat k) v) (bd_equal kt zero) = crispTruth B (k = 0) := by
      rw [bTruth_equal_r181]
      rw [show bTerm (DVec.cons (bSet.of_nat k) v) kt = bSet.of_nat k from bTerm_current_r181 v _,
        bTerm_zero_checked_r192,checkedNat_eq_crisp_r189]
    have hNot : bTruth (DVec.cons (bSet.of_nat k) v) (bd_not (bd_equal kt zero)) =
        (bTruth (DVec.cons (bSet.of_nat k) v) (bd_equal kt zero))ᶜ :=
      boolean_realize_bounded_formula_not (v := DVec.cons (bSet.of_nat k) v) (f := bd_equal kt zero)
    exact hNot.trans ((congrArg (fun x : B => xᶜ) hEq).trans (crisp_not_r197 (B := B) (k = 0)).symm)
  have hLE (k N p : ℕ) :
      bTruth (u k N p) (natLE_f (up nt) pt) = crispTruth B (N ≤ p) :=
    bTruth_natLE_checked_r192 _ _ _ N p
      ((bTerm_up_r181 _ _ nt).trans (bTerm_current_r181 _ _)) (bTerm_current_r181 _ _)
  have hB (k N p : ℕ) :
      bTruth (u k N p) (budget (up3 a) (up3 b) (up2 kt) pt) = crispTruth B (P k p) :=
    hBudget _ _ _ _ _ k p ((bTerm_up3_r181 v _ _ _ a).trans ha) ((bTerm_up3_r181 v _ _ _ b).trans hb)
      ((bTerm_up2_r181 _ _ _ kt).trans (bTerm_current_r181 _ _)) (bTerm_current_r181 _ _)
  unfold eventualBudget_f
  simp only [bTruth_allOmega_r192,bTruth_exOmega_r192,bTruth_imp_r181]
  change (⨅ k : ℕ, bTruth (DVec.cons (bSet.of_nat k) v) (bd_not (bd_equal kt zero)) ⟹
    ⨆ N : ℕ, ⨅ p : ℕ, bTruth (u k N p) (natLE_f (up nt) pt) ⟹
      bTruth (u k N p) (budget (up3 a) (up3 b) (up2 kt) pt)) = _
  simp only [hNE,hLE,hB]
  simp only [← crisp_imp_r190,iInf_crisp_r192,iSup_crisp_r192,EventuallyIntegerBudget]

theorem bTruth_ordinaryLE_checked_r201 {n : ℕ} (v : DVec (V B) n)
    (a b : STerm n) (A C : Set ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C) :
    bTruth v (ordinaryLE_f a b) = crispTruth B (OrdinaryIntegerNull A C) :=
  bTruth_eventualBudget_checked_r201 v a b A C ha hb _ _
    (fun u aTerm bTerm' kt pt k p hA hB hK hP => bTruth_ordinaryBudget_checked_r200 u aTerm bTerm' kt pt A C k p hA hB hK hP)

theorem bTruth_harmonicLE_checked_r201 {n : ℕ} (v : DVec (V B) n)
    (a b : STerm n) (A C : Set ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C) :
    bTruth v (harmonicLE_f a b) = crispTruth B (HarmonicIntegerNull A C) :=
  bTruth_eventualBudget_checked_r201 v a b A C ha hb _ _
    (fun u aTerm bTerm' kt pt k p hA hB hK hP => bTruth_harmonicBudget_checked_r200 u aTerm bTerm' kt pt A C k p hA hB hK hP)

end SetLanguage
end JSP000933
