import JSP000933MixedStepSemantics

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bTruth_naturalRecursion_value_r209 {n k : ℕ} (v : DVec (V B) n)
    (m base result : STerm n) (N M R : ℕ)
    (hm : bTerm v m = bSet.of_nat N) (hb : bTerm v base = bSet.of_nat M)
    (hr : bTerm v result = bSet.of_nat R)
    (params : Fin k → STerm n) (S : ℕ → ℕ → ℕ → B)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d)
    (hStep : StepHasBooleanValue (B := B) (fun a => bTerm v (params a)) S step) :
    bTruth v (naturalRecursion_f m base result params step) =
      recurrenceOfTables B N M R S := by
  rw [← recurrence_graphs_eq_tables_r207]
  change bTruth v (exIn omega fun e =>
    bd_and (successor_f (up m) e) (sEx fun g =>
      bd_and (naturalFunctionOn_f g (up e))
        (bd_and (value_f g zero (up2 base))
          (bd_and (value_f g (up2 m) (up2 result)) (natRecStepsOnly_f m g params step))))) = _
  let eTerm : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let gTerm : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  have hGuard (e : ℕ) :
      bTruth (DVec.cons (bSet.of_nat e) v) (successor_f (up m) eTerm) =
        crispTruth B (e = N+1) := by
    apply bTruth_successor_twoChecked_r192 _ _ _ N e
    · exact (bTerm_up_r181 v _ m).trans hm
    · exact bTerm_current_r181 v _
  simp only [bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ e : ℕ, bTruth (DVec.cons (bSet.of_nat e) v) (successor_f (up m) eTerm) ⊓
    bTruth (DVec.cons (bSet.of_nat e) v) (sEx fun g =>
      bd_and (naturalFunctionOn_f g (up eTerm))
        (bd_and (value_f g zero (up2 base))
          (bd_and (value_f g (up2 m) (up2 result)) (natRecStepsOnly_f m g params step))))) = _
  simp only [hGuard,iSup_crispEquality_select_r193,bTruth_sEx_r181]
  unfold recurrenceOfGraphs
  apply congrArg iSup
  funext G
  let e : V B := bSet.of_nat (N+1)
  let u := DVec.cons G (DVec.cons e v)
  have hd : bTerm u (up eTerm) = bSet.of_nat (N+1) :=
    (bTerm_up_r181 (DVec.cons e v) G eTerm).trans (bTerm_current_r181 v e)
  have hF := bTruth_naturalFunction_checked_r193 u gTerm (up eTerm) N hd
  have hS : bTruth u (natRecStepsOnly_f m gTerm params step) = tableStepValues G N S :=
    (bTruth_natRecSteps_value_r208 v e G m gTerm N hm params S step hStep).trans
      (congrArg (fun g => tableStepValues g N S) (bTerm_current_r181 (DVec.cons e v) G))
  change bTruth u (bd_and (naturalFunctionOn_f gTerm (up eTerm))
    (bd_and (value_f gTerm zero (up2 base))
      (bd_and (value_f gTerm (up2 m) (up2 result)) (natRecStepsOnly_f m gTerm params step)))) = _
  have hg : bTerm u gTerm = G := bTerm_current_r181 (DVec.cons e v) G
  have hm' : bTerm u (up2 m) = bSet.of_nat N := (bTerm_up2_r181 v e G m).trans hm
  have hb' : bTerm u (up2 base) = bSet.of_nat M := (bTerm_up2_r181 v e G base).trans hb
  have hr' : bTerm u (up2 result) = bSet.of_nat R := (bTerm_up2_r181 v e G result).trans hr
  simp only [boolean_realize_bounded_formula_and,hF,hS,value_f,
    boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    bTerm_zero_checked_r192,hg,hm',hb',hr',valueAtNat,inf_assoc]

theorem recurrenceOfTables_crisp_r209 (n base out : ℕ) (S : ℕ → ℕ → ℕ → Prop) :
    recurrenceOfTables B n base out (fun i y z => crispTruth B (S i y z)) =
      crispTruth B (FiniteRecursion n base out S) := by
  rw [← recurrence_graphs_eq_tables_r207]
  exact finiteRecursionValue_crisp_r190 n base out S

end SetLanguage
end JSP000933
