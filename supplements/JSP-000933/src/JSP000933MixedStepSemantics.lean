import JSP000933NaturalStepSemantics
import JSP000933MixedStepRecurrence

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem recurrenceOfTables_maskCongr_r208 {p : B} {S T : ℕ → ℕ → ℕ → B}
    (n base out : ℕ) (h : ∀ i < n, ∀ y z, p ⊓ S i y z = p ⊓ T i y z) :
    p ⊓ recurrenceOfTables B n base out S = p ⊓ recurrenceOfTables B n base out T := by
  apply mask_iSup_congr_r126
  intro f
  apply mask_inf_congr_r126 rfl
  apply mask_iInf_congr_r126
  intro i
  exact h i.val i.isLt (f i.castSucc) (f i.succ)

def StepHasBooleanValue {k : ℕ} (param : Fin k → bSet B) (S : ℕ → ℕ → ℕ → B)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d) : Prop :=
  ∀ {d : ℕ} (w : DVec (V B) d) (params : Fin k → STerm d) (it yt zt : STerm d) (i y z : ℕ),
    (∀ a, bTerm w (params a) = param a) → bTerm w it = bSet.of_nat i →
    bTerm w yt = bSet.of_nat y → bTerm w zt = bSet.of_nat z →
    bTruth w (step params it yt zt) = S i y z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bTruth_natRecSteps_value_r208 {n k : ℕ} (v : DVec (V B) n)
    (e G : V B) (m : STerm n) (g : STerm (n+2)) (N : ℕ)
    (hm : bTerm v m = bSet.of_nat N)
    (params : Fin k → STerm n) (S : ℕ → ℕ → ℕ → B)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d)
    (hStep : StepHasBooleanValue (B := B) (fun a => bTerm v (params a)) S step) :
    bTruth (DVec.cons G (DVec.cons e v)) (natRecStepsOnly_f m g params step) =
      tableStepValues (bTerm (DVec.cons G (DVec.cons e v)) g) N S := by
  let v2 := DVec.cons G (DVec.cons e v)
  have hm2 : bTerm v2 (up2 m) = bSet.of_nat N := (bTerm_up2_r181 v e G m).trans hm
  change bTruth v2 (natRecStepsOnly_f m g params step) = tableStepValues (bTerm v2 g) N S
  unfold natRecStepsOnly_f
  rw [bTruth_boundedForallNat_r191 v2 (up2 m) N hm2]
  unfold tableStepValues
  apply congrArg iInf
  funext i
  simp only [bTruth_allOmega_r192]
  let it : STerm (n+3) := bd_var ⟨0,by omega⟩
  let jt : STerm (n+4) := bd_var ⟨0,by omega⟩
  let yt : STerm (n+5) := bd_var ⟨0,by omega⟩
  let zt : STerm (n+6) := bd_var ⟨0,by omega⟩
  let u (j y z : ℕ) : DVec (V B) (n+6) :=
    DVec.cons (bSet.of_nat z) (DVec.cons (bSet.of_nat y) (DVec.cons (bSet.of_nat j)
      (DVec.cons (bSet.of_nat i.val) v2)))
  have hsucc (j y z : ℕ) :
      bTruth (u j y z) (successor_f (up3 it) (up2 jt)) = crispTruth B (j = i.val+1) := by
    apply bTruth_successor_twoChecked_r192 _ _ _ i.val j
    · simp only [u,it,bTerm_up3_r181,bTerm_current_r181]
    · simp only [u,jt,bTerm_up2_r181,bTerm_current_r181]
  have hS (j y z : ℕ) :
      bTruth (u j y z) (step (fun a => lift_bounded_term (params a) 6) (up3 it) (up yt) zt) =
        S i.val y z := by
    apply hStep _ _ _ _ _ i.val y z
    · intro a
      simp only [u,v2,bTerm_lift6_r194]
    · simp only [u,it,bTerm_up3_r181,bTerm_current_r181]
    · simp only [u,yt,bTerm_up_r181,bTerm_current_r181]
    · simp only [u,zt,bTerm_current_r181]
  change (⨅ j : ℕ, ⨅ y : ℕ, ⨅ z : ℕ, bTruth (u j y z)
    (bd_imp (bd_and (successor_f (up3 it) (up2 jt))
      (bd_and (value_f (up4 g) (up3 it) (up yt)) (value_f (up4 g) (up2 jt) zt)))
      (step (fun a => lift_bounded_term (params a) 6) (up3 it) (up yt) zt))) = _
  simp only [bTruth_imp_r181,boolean_realize_bounded_formula_and,hsucc,hS,
    value_f,boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    u,it,jt,yt,zt,bTerm_up3_r181,bTerm_up2_r181,bTerm_up_r181,bTerm_up4_r194,bTerm_current_r181]
  exact step_guard_select_r194 i.val
    (fun j y z => valueAtNat (bTerm v2 g) i.val y ⊓ valueAtNat (bTerm v2 g) j z)
    (fun y z => S i.val y z)

end SetLanguage
end JSP000933
