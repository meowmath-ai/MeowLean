import JSP000930AnalyticTypedGraphWitness

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem complexRecursion_unique {n k : ℕ} (v : DVec (V B) n)
    (M base result : STerm n) (params : Fin k → STerm n)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d)
    (m : ℕ) (f : ℕ → ComplexBits B) (p : B) (pv : Fin k → bSet B)
    (hM : bTerm v M = bSet.of_nat m) (hbase : bTerm v base = (f 0).name)
    (hparams : ∀ i, bTerm v (params i) = pv i)
    (hstep : ∀ {d : ℕ} (w : DVec (V B) d) (ps : Fin k → STerm d)
      (I C N : STerm d) (i : ℕ) (a : ComplexBits B), i < m →
      (∀ j, bTerm w (ps j) = pv j) → bTerm w I = bSet.of_nat i →
      bTerm w C = (f i).name → bTerm w N = a.name → a.CutOn p →
      p ≤ bTruth w (step ps I C N) → p ≤ a.name =ᴮ (f (i+1)).name)
    (h : p ≤ bTruth v (complexRecursion_f M base result params step)) :
    p ≤ bTerm v result =ᴮ (f m).name := by
  let endN : bSet B := bSet.of_nat (m+1)
  let V1 (x : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat (𝔹 := B) x) v
  let E0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let G0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let Steps : SForm (n+2) :=
    allIn (up2 M) fun i => allIn omega fun j => sAll fun cur => sAll fun next =>
      bd_imp (bd_and (successor_f (up3 i) (up2 j))
        (bd_and (value_f (up4 G0) (up3 i) (up cur)) (value_f (up4 G0) (up2 j) next)))
        (step (fun a => up2 (up2 (up2 (params a)))) (up3 i) (up cur) next)
  let Core : SForm (n+2) := bd_and (typedComplexFunctionOn_f G0 (up E0))
    (bd_and (value_f G0 zero (up2 base)) (bd_and (value_f G0 (up2 M) (up2 result)) Steps))
  have hh : p ≤ bTruth v (exIn omega fun e =>
      bd_and (successor_f (up M) e) (sEx fun _ => Core)) := h
  simp only [bTruth_exOmega_r192,bTruth_and_eq] at hh
  have hsucc (i : ℕ) : bTruth (V1 i) (successor_f (up M) E0) = crispTruth B (i=m+1) :=
    bTruth_successor_twoChecked_r192 (V1 i) (up M) E0 m i
      ((bTerm_up_r181 v (bSet.of_nat i) M).trans hM) (bTerm_current_r181 v (bSet.of_nat i))
  change p ≤ ⨆ i : ℕ, bTruth (V1 i) (successor_f (up M) E0) ⊓
    bTruth (V1 i) (sEx fun _ => Core) at hh
  simp only [hsucc,iSup_crispEquality_select_r193,bTruth_sEx_r181] at hh
  let V2 (g : bSet B) : DVec (V B) (n+2) := DVec.cons g (V1 (m+1))
  let F (g : bSet B) : B := bTruth (V2 g) Core
  obtain ⟨g,hg⟩ := bSet.maximum_principle F (bTruth_body_ext_r191 (V1 (m+1)) Core)
  have hg' : p ≤ bTruth (V2 g) Core := hh.trans hg.le
  let v2 := V2 g
  change p ≤ bTruth v2 Core at hg'
  simp only [Core,bTruth_and_eq] at hg'
  have hG2 : bTerm v2 G0 = g := bTerm_current_r181 (V1 (m+1)) g
  have hM2 : bTerm v2 (up2 M) = bSet.of_nat m := (bTerm_up2_r181 v endN g M).trans hM
  have hE2 : bTerm v2 (up E0) = endN := by
    exact (bTerm_up_r181 (V1 (m+1)) g E0).trans (bTerm_current_r181 v endN)
  have hTyped : p ≤ bTruth v2 (typedComplexFunctionOn_f G0 (up E0)) := hg'.trans inf_le_left
  have hfunc := typedComplexFunction_functional v2 G0 (up E0) p hTyped
  have hfunc' : p ≤ bSet.is_func g := by simpa only [hG2] using hfunc
  have hB : p ≤ bSet.pair (bSet.of_nat 0) (f 0).name ∈ᴮ g := by
    have hb : p ≤ bTruth v2 (value_f G0 zero (up2 base)) :=
      hg'.trans (inf_le_right.trans inf_le_left)
    rw [bTruth_value,hG2,bTerm_zero_checked_r192,(bTerm_up2_r181 v endN g base).trans hbase] at hb
    exact hb
  have hResult : p ≤ bSet.pair (bSet.of_nat m) (bTerm v result) ∈ᴮ g := by
    have hr : p ≤ bTruth v2 (value_f G0 (up2 M) (up2 result)) :=
      hg'.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    rw [bTruth_value,hG2,hM2,bTerm_up2_r181 v endN g result] at hr
    exact hr
  have hSteps : p ≤ bTruth v2 Steps := hg'.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have memStates : ∀ i ≤ m, p ≤ bSet.pair (bSet.of_nat i) (f i).name ∈ᴮ g := by
    intro i hi
    induction i with
    | zero => exact hB
    | succ i ih =>
      have him : i < m := Nat.lt_of_succ_le hi
      have hm' : p ≤ (bSet.of_nat (𝔹 := B) (i+1)) ∈ᴮ bTerm v2 (up E0) := by
        rw [hE2]
        change p ≤ (bSet.of_nat (i+1) : bSet B) ∈ᴮ bSet.of_nat (m+1)
        rw [checkedNat_mem_r174,ite_eq_left (Nat.succ_lt_succ him)]
        exact le_top
      obtain ⟨a,ha,hmem⟩ := typedComplexFunction_totalComplex v2 G0 (up E0)
        (bSet.of_nat (i+1)) p hTyped hm'
      have han : p ≤ bSet.pair (bSet.of_nat (i+1)) a.name ∈ᴮ g := by
        simpa only [hG2] using hmem
      let vi : DVec (V B) (n+3) := DVec.cons (bSet.of_nat (𝔹 := B) i) v2
      let vj : DVec (V B) (n+4) := DVec.cons (bSet.of_nat (𝔹 := B) (i+1)) vi
      let W := complexCoordinates vj (f i).name a.name
      let I0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
      let J0 : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
      let I := up3 I0
      let J := up2 J0
      let C : STerm (n+6) := realCoordinate_f
      let N : STerm (n+6) := imagCoordinate_f
      let GG := up2 (up2 G0)
      let P : Fin k → STerm (n+6) := fun j => up2 (up2 (up2 (params j)))
      have hiW : bTerm W I = bSet.of_nat i := by
        exact (bTerm_up3_r181 vi (bSet.of_nat (i+1)) (f i).name a.name I0).trans
          (bTerm_current_r181 v2 (bSet.of_nat i))
      have hjW : bTerm W J = bSet.of_nat (i+1) := by
        exact (bTerm_up2_r181 vj (f i).name a.name J0).trans
          (bTerm_current_r181 vi (bSet.of_nat (i+1)))
      have hcW : bTerm W C = (f i).name := by
        exact (bTerm_up_r181 (DVec.cons (f i).name vj) a.name
          (bd_var ⟨0,Nat.succ_pos (n+4)⟩)).trans (bTerm_current_r181 vj (f i).name)
      have hnW : bTerm W N = a.name := by
        exact bTerm_current_r181 (DVec.cons (f i).name vj) a.name
      have hgW : bTerm W GG = g := by
        exact (bTerm_up2_r181 vj (f i).name a.name (up2 G0)).trans
          ((bTerm_up2_r181 v2 (bSet.of_nat i) (bSet.of_nat (i+1)) G0).trans hG2)
      have hPS (j : Fin k) : bTerm W (P j) = pv j := by
        exact (bTerm_up2_r181 vj (f i).name a.name (up2 (up2 (params j)))).trans
          ((bTerm_up2_r181 v2 (bSet.of_nat i) (bSet.of_nat (i+1)) (up2 (params j))).trans
            ((bTerm_up2_r181 v endN g (params j)).trans (hparams j)))
      have hh := hSteps
      unfold Steps at hh
      rw [bTruth_boundedForallNat_r191 v2 (up2 M) m hM2] at hh
      have hI := hh.trans (iInf_le _ (⟨i,him⟩ : Fin m))
      rw [bTruth_allOmega_r192] at hI
      have hJ := hI.trans (iInf_le _ (i+1))
      simp only [bTruth_sAll_r181] at hJ
      have hC := hJ.trans (iInf_le _ (f i).name)
      have hN := hC.trans (iInf_le _ a.name)
      change p ≤ bTruth W (bd_imp (bd_and (successor_f I J)
        (bd_and (value_f GG I C) (value_f GG J N))) (step P I C N)) at hN
      simp only [bTruth_imp_r181,bTruth_and_eq,bTruth_value,hgW,hiW,hjW,hcW,hnW] at hN
      rw [bTruth_successor_twoChecked_r192 W I J i (i+1) hiW hjW,
        show crispTruth B (i+1=i+1) = ⊤ by simp [crispTruth],top_inf_eq,← _root_.deduction] at hN
      have hs := (le_inf le_rfl (le_inf (ih (Nat.le_of_lt him)) han)).trans hN
      have hEq := hstep W P I C N i a him hPS hiW hcW hnW ha hs
      exact bSet.subst_congr_mem_left' (bSet.pair_congr (le_top.trans bSet.bv_refl) hEq) han
  exact bSet.eq_of_is_func_of_eq hfunc' (le_top.trans bSet.bv_refl) hResult (memStates m le_rfl)

end JSP000930.AnalyticSyntax
