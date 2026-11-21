import JSP000930AnalyticComplexSelectors

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem bTruth_normError_checked {n : ℕ} (v : DVec (V B) n)
    (D K : STerm n) (d : ComplexBits B) (k : ℕ) (p : B)
    (hD : bTerm v D = d.name) (hK : bTerm v K = bSet.of_nat k) (hd : d.CutOn p) :
    let x := weightedRationalSet (mulCutBits d.normSq (checkedRealBits ((k : ℝ)^2)))
    let one := weightedRationalSet (checkedRealBits (B := B) 1)
    p ⊓ bTruth v (normError_f D K) = p ⊓ ((x ⊆ᴮ one) ⊓ (x =ᴮ one)ᶜ) := by
  let kk := k*k
  let v1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) kk) v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let O : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let v2 (i : ℕ) : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) i) v1
  unfold normError_f
  rw [bTruth_natExprSelect_checked v squareNatExpr (fun _ : Fin 1 => K)
    (fun _ : Fin 1 => D) _ (fun _ => k) (fun _ => hK)]
  have h1 (i : ℕ) : bTruth (v2 i) (successor_f zero O) = crispTruth B (i=1) :=
    bTruth_successor_twoChecked_r192 (v2 i) zero O 0 i (bTerm_zero_checked_r192 (v2 i))
      (bTerm_current_r181 v1 (bSet.of_nat i))
  change p ⊓ bTruth v1 (exIn omega fun one => bd_and (successor_f zero one)
    (scaledNormCompare_f true (up (up D)) (up T) one)) = _
  rw [bTruth_exOmega_r192]
  simp only [bTruth_and_eq]
  change (p ⊓ (⨆ i : ℕ, bTruth (v2 i) (successor_f zero O) ⊓
    bTruth (v2 i) (scaledNormCompare_f true (up (up D)) (up T) O))) = _
  simp only [h1,iSup_crispEquality_select_r193]
  have hD' : bTerm (v2 1) (up (up D)) = d.name := by
    exact (bTerm_up_r181 v1 (bSet.of_nat 1) (up D)).trans
      ((bTerm_up_r181 v (bSet.of_nat kk) D).trans hD)
  have hK' : bTerm (v2 1) (up T) = bSet.of_nat kk := by
    exact (bTerm_up_r181 v1 (bSet.of_nat 1) T).trans (bTerm_current_r181 v (bSet.of_nat kk))
  rw [bTruth_scaledNormCompare_checked (v2 1) true (up (up D)) (up T) O d kk 1 p
      hD' hK' (bTerm_current_r181 v1 (bSet.of_nat 1)) hd]
  simp [kk,pow_two]

theorem bTruth_evaluationBudget_weighted {n : ℕ} (v : DVec (V B) n)
    (A Z W K N : STerm n) (a : ℕ → ComplexBits B) (z w : ComplexBits B)
    (k i : ℕ) (p : B)
    (hZ : bTerm v Z = z.name) (hW : p ≤ bTerm v W =ᴮ w.name)
    (hK : bTerm v K = bSet.of_nat k) (hN : bTerm v N = bSet.of_nat i)
    (ha : ∀ j < i,(a j).CutOn p) (hz : z.CutOn p) (hw : w.CutOn p)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hVal : ∀ j < i,p ≤ bSet.pair (bSet.of_nat j) (a j).name ∈ᴮ bTerm v A) :
    p ⊓ bTruth v (evaluationBudget_f A Z W K N) =
      p ⊓ evalErrorBits (taylorPrefixBits a z i) w k := by
  let pref := taylorPrefixBits a z i
  let d := pref.sub w
  let v1 : DVec (V B) (n+1) := DVec.cons pref.name v
  let v2 : DVec (V B) (n+2) := DVec.cons w.neg.name v1
  let v3 : DVec (V B) (n+3) := DVec.cons d.name v2
  let T1 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let T2 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let T3 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let P : Fin 5 → STerm n := ![A,Z,W,K,N]
  let P1 : Fin 3 → STerm (n+1) := ![up W,up K,T1]
  let P2 : Fin 3 → STerm (n+2) := ![up (P1 1),up (P1 2),T2]
  have hp : pref.CutOn p := taylorPrefixBits_cutOn hz ha i le_rfl
  have hw1 : p ≤ bTerm v1 (P1 0) =ᴮ w.name := by
    change p ≤ bTerm v1 (up W) =ᴮ w.name
    rw [bTerm_up_r181 v pref.name W]
    exact hW
  have hp2 : bTerm v2 (P2 1) = pref.name := by
    exact (bTerm_up_r181 v1 w.neg.name T1).trans (bTerm_current_r181 v pref.name)
  have hw2 : bTerm v2 (P2 2) = w.neg.name := bTerm_current_r181 v1 w.neg.name
  unfold evaluationBudget_f
  rw [bTruth_selectTaylorPrefix_weighted v P _ 0 1 4 (bTerm v A) a z i p rfl hZ hN
    ha hz hF hVal]
  change p ⊓ bTruth v1 (selectComplex_f P1 (fun r NW => complexNeg_f (r 0) NW)
    (fun r NW => selectComplex_f (fun i => ![r 1,r 2,NW] i)
      (fun w D => complexAdd_f (w 1) (w 2) D) (fun w D => normError_f D (w 0)))) = _
  rw [bTruth_selectComplexNeg_weighted v1 P1 _ 0 w p hw1 hw]
  change p ⊓ bTruth v2 (selectComplex_f P2 (fun w D => complexAdd_f (w 1) (w 2) D)
    (fun w D => normError_f D (w 0))) = _
  rw [bTruth_selectComplexAdd_weighted v2 P2 _ 1 2 pref w.neg p hp2 hw2 hp
    (ComplexBits.neg_cutOn hw)]
  change p ⊓ bTruth v3 (normError_f T3 (up (P2 0))) = _
  have hkn : bTerm v3 (up (P2 0)) = bSet.of_nat k := by
    exact (bTerm_up_r181 v2 d.name (P2 0)).trans
      ((bTerm_up_r181 v1 w.neg.name (P1 1)).trans ((bTerm_up_r181 v pref.name K).trans hK))
  exact bTruth_normError_checked v3 T3 (up (P2 0)) d k p
    (bTerm_current_r181 v2 d.name) hkn (ComplexBits.sub_cutOn hp hw)

end JSP000930.AnalyticSyntax
