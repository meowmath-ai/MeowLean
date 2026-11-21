import JSP000930AnalyticFiniteComplexGraph

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

set_option backward.isDefEq.respectTransparency false

theorem forces_complexRecursion_graph {n k : ℕ} (v : DVec (V B) n)
    (M base result : STerm n) (params : Fin k → STerm n)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d)
    (m : ℕ) (f : ℕ → ComplexBits B) (p : B) (pv : Fin k → bSet B)
    (hM : bTerm v M = bSet.of_nat m) (hbase : bTerm v base = (f 0).name)
    (hresult : bTerm v result = (f m).name) (hparams : ∀ i, bTerm v (params i) = pv i)
    (hf : ∀ i ≤ m, (f i).CutOn p)
    (hstep : ∀ {d : ℕ} (w : DVec (V B) d) (ps : Fin k → STerm d)
      (I C N : STerm d) (i : ℕ), i < m → (∀ j, bTerm w (ps j) = pv j) →
      bTerm w I = bSet.of_nat i → bTerm w C = (f i).name → bTerm w N = (f (i+1)).name →
      p ≤ bTruth w (step ps I C N)) :
    p ≤ bTruth v (complexRecursion_f M base result params step) := by
  let endN := (bSet.of_nat (𝔹 := B) (m+1))
  let G := finiteComplexGraph (m+1) f
  let v1 : DVec (V B) (n+1) := DVec.cons endN v
  let v2 : DVec (V B) (n+2) := DVec.cons G v1
  let E0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let G0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  unfold complexRecursion_f
  rw [bTruth_exOmega_r192]
  apply le_iSup_of_le (m+1)
  simp only [bTruth_and_eq]
  refine le_inf ?_ ?_
  · rw [bTruth_successor_twoChecked_r192 v1 (up M) E0 m (m+1)
      ((bTerm_up_r181 v endN M).trans hM) (bTerm_current_r181 v endN)]
    simp [crispTruth]
  rw [bTruth_sEx_r181]
  apply le_iSup_of_le G
  simp only [bTruth_and_eq]
  have hG : bTerm v2 G0 = G := bTerm_current_r181 v1 G
  have hE : bTerm v2 (up E0) = bSet.of_nat (m+1) := by
    exact (bTerm_up_r181 v1 G E0).trans (bTerm_current_r181 v endN)
  have hm : bTerm v2 (up2 M) = bSet.of_nat m :=
    (bTerm_up2_r181 v endN G M).trans hM
  let z0 : Fin (m+1) := ⟨0,Nat.succ_pos m⟩
  let zm : Fin (m+1) := ⟨m,Nat.lt_succ_self m⟩
  refine le_inf (forces_typedFiniteComplexGraph v2 G0 (up E0) (m+1) f p hG hE
    (fun i => hf i.val (Nat.le_of_lt_succ i.isLt))) (le_inf ?_ (le_inf ?_ ?_))
  · have hb : bTerm v2 (up2 base) = (f 0).name := (bTerm_up2_r181 v endN G base).trans hbase
    rw [bTruth_value,hG,bTerm_zero_checked_r192,hb]
    have hz := finiteComplexGraph_value (m+1) f z0 (f 0).name
    exact le_top.trans (bSet.bv_refl.trans_eq hz.symm)
  · have hr : bTerm v2 (up2 result) = (f m).name := (bTerm_up2_r181 v endN G result).trans hresult
    rw [bTruth_value,hG,hm,hr]
    have hz := finiteComplexGraph_value (m+1) f zm (f m).name
    exact le_top.trans (bSet.bv_refl.trans_eq hz.symm)
  · rw [bTruth_boundedForallNat_r191 v2 (up2 M) m hm]
    refine le_iInf fun i : Fin m => ?_
    rw [bTruth_allOmega_r192]
    refine le_iInf fun j : ℕ => ?_
    simp only [bTruth_sAll_r181,bTruth_imp_r181,bTruth_and_eq]
    refine le_iInf fun cur : bSet B => le_iInf fun next : bSet B => ?_
    rw [← _root_.deduction]
    let vi : DVec (V B) (n+3) := DVec.cons (bSet.of_nat (𝔹 := B) i.val) v2
    let vj : DVec (V B) (n+4) := DVec.cons (bSet.of_nat (𝔹 := B) j) vi
    let V := complexCoordinates vj cur next
    let I0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    let J0 : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
    let I := up3 I0
    let J := up2 J0
    let C : STerm (n+6) := realCoordinate_f
    let N : STerm (n+6) := imagCoordinate_f
    let GG := up2 (up2 G0)
    let P : Fin k → STerm (n+6) := fun a => up2 (up2 (up2 (params a)))
    have hiV : bTerm V I = bSet.of_nat i.val := by
      simp only [V,complexCoordinates,vj,vi,I,I0,bTerm_up3_r181,bTerm_current_r181]
    have hjV : bTerm V J = bSet.of_nat j := by
      simp only [V,complexCoordinates,vj,J,J0,bTerm_up2_r181,bTerm_current_r181]
    have hcV : bTerm V C = cur := by
      simp only [V,complexCoordinates,C,realCoordinate_f,bTerm_up_r181,bTerm_current_r181]
    have hnV : bTerm V N = next := by
      simp only [V,complexCoordinates,N,imagCoordinate_f,bTerm_current_r181]
    have hgV : bTerm V GG = G := by
      simp only [V,complexCoordinates,vj,vi,GG,bTerm_up2_r181,hG]
    change p ⊓ (bTruth V (successor_f I J) ⊓
      (bTruth V (value_f GG I C) ⊓ bTruth V (value_f GG J N))) ≤ bTruth V (step P I C N)
    rw [bTruth_successor_twoChecked_r192 V I J i.val j hiV hjV,
      bTruth_value,bTruth_value,hgV,hiV,hjV,hcV,hnV]
    by_cases hji : j = i.val+1
    · subst j
      let ix : Fin (m+1) := ⟨i.val,i.isLt.trans (Nat.lt_succ_self m)⟩
      let jx : Fin (m+1) := ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
      rw [show crispTruth B (i.val+1 = i.val+1) = ⊤ by simp [crispTruth],top_inf_eq]
      rw [show (bSet.pair (bSet.of_nat i.val) cur ∈ᴮ G) = (cur =ᴮ (f i.val).name)
        from finiteComplexGraph_value (m+1) f ix cur]
      rw [show (bSet.pair (bSet.of_nat (i.val+1)) next ∈ᴮ G) = (next =ᴮ (f (i.val+1)).name)
        from finiteComplexGraph_value (m+1) f jx next]
      let e := p ⊓ ((cur =ᴮ (f i.val).name) ⊓ (next =ᴮ (f (i.val+1)).name))
      let W := complexCoordinates vj (f i.val).name (f (i.val+1)).name
      have hp : e ≤ p := inf_le_left
      have hPS (a : Fin k) : bTerm W (P a) = pv a := by
        simp only [W,complexCoordinates,vj,vi,v2,v1,P,bTerm_up2_r181,hparams]
      have hIW : bTerm W I = bSet.of_nat i.val := by
        simp only [W,complexCoordinates,vj,vi,I,I0,bTerm_up3_r181,bTerm_current_r181]
      have hCW : bTerm W C = (f i.val).name := by
        simp only [W,complexCoordinates,C,realCoordinate_f,bTerm_up_r181,bTerm_current_r181]
      have hNW : bTerm W N = (f (i.val+1)).name := by
        simp only [W,complexCoordinates,N,imagCoordinate_f,bTerm_current_r181]
      have hs := hp.trans (hstep W P I C N i.val i.isLt hPS hIW hCW hNW)
      have hMask := bTruth_twoMask vj cur next (f i.val).name (f (i.val+1)).name
        (step P I C N) e (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
      exact (le_inf le_rfl hs).trans (hMask.symm.le.trans inf_le_right)
    · simp [crispTruth,hji]

end JSP000930.AnalyticSyntax
