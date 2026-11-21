import JSP000930AnalyticBudgetSelectors

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_scaledNormCompare_checked {n : ℕ} (v : DVec (V B) n)
    (strict : Bool) (C RP KQ : STerm n) (z : ComplexBits B) (r k : ℕ) (p : B)
    (hC : bTerm v C = z.name) (hR : bTerm v RP = bSet.of_nat r)
    (hK : bTerm v KQ = bSet.of_nat k) (hz : z.CutOn p) :
    let L := weightedRationalSet (mulCutBits z.normSq (checkedRealBits (r : ℝ)))
    let R := weightedRationalSet (checkedRealBits (B := B) (k : ℝ))
    p ⊓ bTruth v (scaledNormCompare_f strict C RP KQ) =
      p ⊓ (if strict then (L ⊆ᴮ R) ⊓ (L =ᴮ R)ᶜ else L ⊆ᴮ R) := by
  let P : Fin 3 → STerm n := ![C,RP,KQ]
  let q1 := weightedRationalSet z.normSq
  let q2 := weightedRationalSet (checkedRealBits (B := B) (r : ℝ))
  let q3 := mulCutName z.normSq (checkedRealBits (r : ℝ))
  let q4 := weightedRationalSet (checkedRealBits (B := B) (k : ℝ))
  let v1 : DVec (V B) (n+1) := DVec.cons q1 v
  let v2 : DVec (V B) (n+2) := DVec.cons q2 v1
  let v3 : DVec (V B) (n+3) := DVec.cons q3 v2
  let v4 : DVec (V B) (n+4) := DVec.cons q4 v3
  let T1 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let T2 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let T3 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let T4 : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let P1 : Fin 3 → STerm (n+1) := ![up RP,up KQ,T1]
  let P2 : Fin 3 → STerm (n+2) := ![up (P1 1),up (P1 2),T2]
  let P3 : Fin 2 → STerm (n+3) := ![up (P2 0),T3]
  have hr1 : bTerm v1 (P1 0) = bSet.of_nat r :=
    (bTerm_up_r181 v q1 RP).trans hR
  have hk3 : bTerm v3 (P3 0) = bSet.of_nat k := by
    exact (bTerm_up_r181 v2 q3 (P2 0)).trans
      ((bTerm_up_r181 v1 q2 (P1 1)).trans ((bTerm_up_r181 v q1 KQ).trans hK))
  have hq1 : bTerm v2 (P2 1) = q1 := by
    exact (bTerm_up_r181 v1 q2 T1).trans (bTerm_current_r181 v q1)
  have hq2 : bTerm v2 (P2 2) = q2 := bTerm_current_r181 v1 q2
  unfold scaledNormCompare_f
  rw [bTruth_selectNormSq_weighted v P _ 0 z p hC hz]
  change p ⊓ bTruth v1 (selectReal_f P1 (fun u P => realNat_f (u 0) P)
    (fun u P => selectReal_f (fun i => ![u 1,u 2,P] i)
      (fun w U => realMul_f (w 1) (w 2) U)
      (fun w U => selectReal_f (fun i => ![w 0,U] i)
        (fun q V => realNat_f (q 0) V)
        (fun q V => if strict then realLT_f (q 1) V else realLE_f (q 1) V)))) = _
  rw [bTruth_selectRealNat_weighted v1 P1 _ 0 r p hr1]
  change p ⊓ bTruth v2 (selectReal_f P2 (fun w U => realMul_f (w 1) (w 2) U)
    (fun w U => selectReal_f (fun i => ![w 0,U] i) (fun q V => realNat_f (q 0) V)
      (fun q V => if strict then realLT_f (q 1) V else realLE_f (q 1) V))) = _
  rw [bTruth_selectMul_weighted v2 P2 _ 1 2 z.normSq (checkedRealBits (r : ℝ)) p
    hq1 hq2 (ComplexBits.normSq_cutOn hz) (properCutOn_mono le_top (checkedRealBits_properCut r))]
  change p ⊓ bTruth v3 (selectReal_f P3 (fun q V => realNat_f (q 0) V)
    (fun q V => if strict then realLT_f (q 1) V else realLE_f (q 1) V)) = _
  rw [bTruth_selectRealNat_weighted v3 P3 _ 0 k p hk3]
  change p ⊓ bTruth v4 (if strict then realLT_f (up T3) T4 else realLE_f (up T3) T4) = _
  have h3 : bTerm v4 (up T3) = q3 :=
    (bTerm_up_r181 v3 q4 T3).trans (bTerm_current_r181 v2 q3)
  have h4 : bTerm v4 T4 = q4 := bTerm_current_r181 v3 q4
  cases strict
  · change p ⊓ bTruth v4 (realLE_f (up T3) T4) = _
    rw [bTruth_realLE,h3,h4]
    rfl
  · change p ⊓ bTruth v4 (realLT_f (up T3) T4) = _
    rw [bTruth_realLT,h3,h4]
    rfl

theorem bTruth_radiusSquared_checked {n : ℕ} (v : DVec (V B) n)
    (C RP KQ : STerm n) (z : ComplexBits B) (r k : ℕ) (p : B)
    (hC : bTerm v C = z.name) (hR : bTerm v RP = bSet.of_nat r)
    (hK : bTerm v KQ = bSet.of_nat k) (hz : z.CutOn p) :
    p ⊓ bTruth v (radiusSquared_f C RP KQ) =
      p ⊓ (weightedRationalSet (mulCutBits z.normSq (checkedRealBits (r : ℝ))) ⊆ᴮ
        weightedRationalSet (checkedRealBits (k : ℝ))) := by
  simpa [radiusSquared_f] using bTruth_scaledNormCompare_checked v false C RP KQ z r k p hC hR hK hz

theorem bTruth_radiusCoefficient_checked {n : ℕ} (v : DVec (V B) n)
    (C R K N : STerm n) (z : ComplexBits B) (r k i : ℕ) (p : B)
    (hC : bTerm v C = z.name) (hR : bTerm v R = bSet.of_nat r)
    (hK : bTerm v K = bSet.of_nat k) (hN : bTerm v N = bSet.of_nat i)
    (hz : z.CutOn p) :
    p ⊓ bTruth v (radiusCoefficient_f C R K N) = p ⊓ radiusBudgetBits z r k i := by
  let RP := r^i * r^i
  let KQ := k*k
  let v1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) RP) v
  let v2 : DVec (V B) (n+2) := DVec.cons (bSet.of_nat (𝔹 := B) KQ) v1
  let T1 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let T2 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let I : Fin 2 → ℕ := ![r,i]
  let P : Fin 2 → STerm n := ![R,N]
  let Q : Fin 2 → STerm n := ![C,K]
  have hp : ∀ j, bTerm v (P j) = bSet.of_nat (I j) := by
    intro j
    fin_cases j
    · exact hR
    · exact hN
  unfold radiusCoefficient_f
  rw [bTruth_natExprSelect_checked v powSquareNatExpr P Q _ I hp]
  change p ⊓ bTruth v1 (natExprSelect_f squareNatExpr (fun _ : Fin 1 => up K)
    (fun j => ![up C,T1] j) (fun u h => radiusSquared_f (u 0) (u 1) h)) = _
  rw [bTruth_natExprSelect_checked v1 squareNatExpr (fun _ : Fin 1 => up K)
    (fun j => ![up C,T1] j) _ (fun _ => k)
    (fun _ => (bTerm_up_r181 v (bSet.of_nat RP) K).trans hK)]
  change p ⊓ bTruth v2 (radiusSquared_f (up (up C)) (up T1) T2) = _
  have hC' : bTerm v2 (up (up C)) = z.name := by
    exact (bTerm_up_r181 v1 (bSet.of_nat KQ) (up C)).trans
      ((bTerm_up_r181 v (bSet.of_nat RP) C).trans hC)
  have hR' : bTerm v2 (up T1) = bSet.of_nat RP := by
    exact (bTerm_up_r181 v1 (bSet.of_nat KQ) T1).trans
      (bTerm_current_r181 v (bSet.of_nat RP))
  rw [bTruth_radiusSquared_checked v2 (up (up C)) (up T1) T2 z RP KQ p hC' hR'
    (bTerm_current_r181 v1 (bSet.of_nat KQ)) hz]
  simp [radiusBudgetBits,RP,KQ,pow_two]

end JSP000930.AnalyticSyntax
