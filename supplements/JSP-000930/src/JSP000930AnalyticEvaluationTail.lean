import JSP000930AnalyticEvaluationBudget

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def EvalErrorTail (a : ℕ → ComplexBits B) (z w : ComplexBits B) (k N : ℕ) : B :=
  ⨅ i : ℕ, if N ≤ i then evalErrorBits (taylorPrefixBits a z i) w k else ⊤

def EvalNativeOn (p : B) (a : ℕ → ComplexBits B) (z w : ComplexBits B) : Prop :=
  ∀ k : ℕ, 0 < k → p ≤ ⨆ N : ℕ, EvalErrorTail a z w k N

theorem EvalErrorTail_project {a : ℕ → ComplexBits B} {z w : ComplexBits B}
    {k N i : ℕ} {p : B} (hp : p ≤ EvalErrorTail a z w k N) (hi : N ≤ i) :
    p ≤ evalErrorBits (taylorPrefixBits a z i) w k := by
  simpa only [ite_eq_left hi] using hp.trans (iInf_le
    (fun j : ℕ => if N ≤ j then evalErrorBits (taylorPrefixBits a z j) w k else ⊤) i)

theorem EvalErrorTail_intro {a : ℕ → ComplexBits B} {z w : ComplexBits B} {k N : ℕ}
    {p : B} (h : ∀ i, N ≤ i → p ≤ evalErrorBits (taylorPrefixBits a z i) w k) :
    p ≤ EvalErrorTail a z w k N := by
  unfold EvalErrorTail
  refine le_iInf fun i => ?_
  by_cases hi : N ≤ i
  · simpa only [ite_eq_left hi] using h i hi
  · simp [hi]

end JSP000930.BooleanAnalysis

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem inf_iInf_nat' (p : B) (F : ℕ → B) :
    p ⊓ (⨅ n : ℕ, F n) = ⨅ n : ℕ, p ⊓ F n := by
  apply le_antisymm
  · exact le_iInf fun n => inf_le_inf_left _ (iInf_le _ n)
  · exact le_inf ((iInf_le _ 0).trans inf_le_left)
      (le_iInf fun n => (iInf_le _ n).trans inf_le_right)

theorem bTruth_evalTail_weighted {n : ℕ} (v : DVec (V B) n)
    (A Z W K N : STerm n) (a : ℕ → ComplexBits B) (z w : ComplexBits B)
    (k cutoff : ℕ) (p : B)
    (hZ : bTerm v Z = z.name) (hW : p ≤ bTerm v W =ᴮ w.name)
    (hK : bTerm v K = bSet.of_nat k) (hN : bTerm v N = bSet.of_nat cutoff)
    (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (hw : w.CutOn p)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hVal : ∀ j,p ≤ bSet.pair (bSet.of_nat j) (a j).name ∈ᴮ bTerm v A) :
    p ⊓ bTruth v (evalTail_f A Z W K N) = p ⊓ EvalErrorTail a z w k cutoff := by
  simp only [evalTail_f,bTruth_allOmega_r192,EvalErrorTail]
  rw [inf_iInf_nat',inf_iInf_nat']
  apply iInf_congr
  intro i
  let V : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) i) v
  let I : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hI : bTerm V I = bSet.of_nat i := bTerm_current_r181 v (bSet.of_nat i)
  have hN' : bTerm V (up N) = bSet.of_nat cutoff :=
    (bTerm_up_r181 v (bSet.of_nat i) N).trans hN
  change p ⊓ bTruth V (bd_imp (natLE_f (up N) I)
    (evaluationBudget_f (up A) (up Z) (up W) (up K) I)) = _
  rw [bTruth_imp_r181,bTruth_natLE_checked_r192 V (up N) I cutoff i hN' hI]
  by_cases h : cutoff ≤ i
  · simp only [ite_eq_left h,crispTruth,h,ite_true,imp,compl_top,bot_sup_eq]
    have he : bTerm V (up A) = bTerm v A := bTerm_up_r181 v (bSet.of_nat i) A
    exact bTruth_evaluationBudget_weighted V (up A) (up Z) (up W) (up K) I a z w k i p
      ((bTerm_up_r181 v (bSet.of_nat i) Z).trans hZ)
      (by rw [bTerm_up_r181 v (bSet.of_nat i) W]; exact hW)
      ((bTerm_up_r181 v (bSet.of_nat i) K).trans hK) hI (fun j _ => ha j) hz hw
      (by rw [he]; exact hF) (fun j _ => by rw [he]; exact hVal j)
  · simp [h,crispTruth,imp]

theorem forces_evalAllTail_iff {n : ℕ} (v : DVec (V B) n) (A Z W : STerm n)
    (a : ℕ → ComplexBits B) (z w : ComplexBits B) (p : B)
    (hZ : bTerm v Z = z.name) (hW : p ≤ bTerm v W =ᴮ w.name)
    (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (hw : w.CutOn p)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hVal : ∀ j,p ≤ bSet.pair (bSet.of_nat j) (a j).name ∈ᴮ bTerm v A) :
    p ≤ bTruth v (evalAllTail_f A Z W) ↔ EvalNativeOn p a z w := by
  let env (k : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) k) v
  let K : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let N : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let F : SForm (n+1) := exIn omega fun N0 => evalTail_f (up2 A) (up2 Z) (up2 W) (up K) N0
  have hTail (k : ℕ) : p ⊓ bTruth (env k) F =
      p ⊓ (⨆ N0 : ℕ,EvalErrorTail a z w k N0) := by
    unfold F
    rw [bTruth_exOmega_r192]
    rw [inf_iSup_eq,inf_iSup_eq]
    apply iSup_congr
    intro N0
    let D : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) N0) (env k)
    change p ⊓ bTruth D (evalTail_f (up2 A) (up2 Z) (up2 W) (up K) N) = _
    have hA : bTerm D (up2 A) = bTerm v A :=
      bTerm_up2_r181 v (bSet.of_nat k) (bSet.of_nat N0) A
    exact bTruth_evalTail_weighted D (up2 A) (up2 Z) (up2 W) (up K) N a z w k N0 p
      ((bTerm_up2_r181 v (bSet.of_nat k) (bSet.of_nat N0) Z).trans hZ)
      (by rw [bTerm_up2_r181 v (bSet.of_nat k) (bSet.of_nat N0) W]; exact hW)
      ((bTerm_up_r181 (env k) (bSet.of_nat N0) K).trans (bTerm_current_r181 v (bSet.of_nat k)))
      (bTerm_current_r181 (env k) (bSet.of_nat N0)) ha hz hw
      (by rw [hA]; exact hF) (fun j => by rw [hA]; exact hVal j)
  have hK (k : ℕ) : bTruth (env k) (bd_not (bd_equal K zero)) = (crispTruth B (k=0))ᶜ := by
    have h : bTruth (env k) (bd_not (bd_equal K zero)) =
        (bTruth (env k) (bd_equal K zero))ᶜ := boolean_realize_bounded_formula_not
    rw [h,bTruth_equal_r181,bTerm_current_r181 v (bSet.of_nat k),
      bTerm_zero_checked_r192,checkedNat_eq_crisp_r189]
  rw [evalAllTail_f,bTruth_allOmega_r192]
  constructor
  · intro h k hk
    have h' := h.trans (iInf_le _ k)
    change p ≤ bTruth (env k) (bd_imp (bd_not (bd_equal K zero)) F) at h'
    rw [bTruth_imp_r181,hK] at h'
    have hk' : k ≠ 0 := Nat.ne_of_gt hk
    simp only [crispTruth,hk',ite_false,compl_bot,imp,compl_top,bot_sup_eq] at h'
    exact (le_inf le_rfl h').trans ((hTail k).le.trans inf_le_right)
  · intro h
    refine le_iInf fun k => ?_
    change p ≤ bTruth (env k) (bd_imp (bd_not (bd_equal K zero)) F)
    rw [bTruth_imp_r181,hK]
    by_cases hk : k = 0
    · simp [crispTruth,hk,imp]
    · simp only [crispTruth,hk,ite_false,compl_bot,imp,compl_top,bot_sup_eq]
      exact (le_inf le_rfl (h k (Nat.pos_of_ne_zero hk))).trans ((hTail k).symm.le.trans inf_le_right)

end JSP000930.AnalyticSyntax
