import JSP000933MixedBudgetValues
import JSP000933ExactGenericGraphOrder

open Fol Lattice
open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def mixedEventualBudgetValue (T : ℕ → ℕ → B) : B :=
  ⨅ k : ℕ, imp (crispTruth B (k ≠ 0))
    (⨆ lo : ℕ, ⨅ p : ℕ, imp (crispTruth B (lo ≤ p)) (T k p))

theorem bTruth_mixedEventualBudget_r213 {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (budget : ∀ {d : ℕ}, STerm d → STerm d → STerm d → STerm d → SForm d)
    (T : bSet B → bSet B → ℕ → ℕ → B)
    (hT : ∀ {d : ℕ} (w : DVec (V B) d) (aTerm bTerm' kt pt : STerm d) (k p : ℕ),
      bTerm w kt = bSet.of_nat k → bTerm w pt = bSet.of_nat p →
      bTruth w (budget aTerm bTerm' kt pt) = T (bTerm w aTerm) (bTerm w bTerm') k p) :
    bTruth v (eventualBudget_f a b budget) = mixedEventualBudgetValue (T (bTerm v a) (bTerm v b)) := by
  let kt : STerm (n+1) := bd_var ⟨0,by omega⟩
  let nt : STerm (n+2) := bd_var ⟨0,by omega⟩
  let pt : STerm (n+3) := bd_var ⟨0,by omega⟩
  let u (k lo p : ℕ) : DVec (V B) (n+3) :=
    DVec.cons (bSet.of_nat p) (DVec.cons (bSet.of_nat lo) (DVec.cons (bSet.of_nat k) v))
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
  have hLE (k lo p : ℕ) :
      bTruth (u k lo p) (natLE_f (up nt) pt) = crispTruth B (lo ≤ p) :=
    bTruth_natLE_checked_r192 _ _ _ lo p ((bTerm_up_r181 _ _ nt).trans (bTerm_current_r181 _ _))
      (bTerm_current_r181 _ _)
  have hB (k lo p : ℕ) :
      bTruth (u k lo p) (budget (up3 a) (up3 b) (up2 kt) pt) = T (bTerm v a) (bTerm v b) k p := by
    have hk : bTerm (u k lo p) (up2 kt) = bSet.of_nat k :=
      (bTerm_up2_r181 (DVec.cons (bSet.of_nat k) v) _ _ kt).trans (bTerm_current_r181 v _)
    have hp : bTerm (u k lo p) pt = bSet.of_nat p := bTerm_current_r181 _ _
    rw [hT (u k lo p) _ _ _ _ k p hk hp]
    rw [show bTerm (u k lo p) (up3 a) = bTerm v a from bTerm_up3_r181 v _ _ _ a,
      show bTerm (u k lo p) (up3 b) = bTerm v b from bTerm_up3_r181 v _ _ _ b]
  simp only [eventualBudget_f,bTruth_allOmega_r192,bTruth_exOmega_r192,bTruth_imp_r181]
  change (⨅ k : ℕ, bTruth (DVec.cons (bSet.of_nat k) v) (bd_not (bd_equal kt zero)) ⟹
    ⨆ lo : ℕ, ⨅ p : ℕ, bTruth (u k lo p) (natLE_f (up nt) pt) ⟹
      bTruth (u k lo p) (budget (up3 a) (up3 b) (up2 kt) pt)) = _
  simp only [hNE,hLE,hB,mixedEventualBudgetValue]

noncomputable def actualOrdLEValue (A C : bSet B) : B :=
  mixedEventualBudgetValue (mixedOrdinaryBudgetValue A C)

noncomputable def actualHarLEValue (A C : bSet B) : B :=
  mixedEventualBudgetValue (mixedHarmonicBudgetValue A C)

@[simp] theorem bTruth_actualOrdLE_r213 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (ordinaryLE_f a b) = actualOrdLEValue (bTerm v a) (bTerm v b) :=
  bTruth_mixedEventualBudget_r213 v a b (fun a b k p => ordinaryBudget_f a b k p)
    mixedOrdinaryBudgetValue bTruth_mixedOrdinaryBudget_r212

@[simp] theorem bTruth_actualHarLE_r213 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (harmonicLE_f a b) = actualHarLEValue (bTerm v a) (bTerm v b) :=
  bTruth_mixedEventualBudget_r213 v a b (fun a b k p => harmonicBudget_f a b k p)
    mixedHarmonicBudgetValue bTruth_mixedHarmonicBudget_r212

noncomputable def actualPreserveReflectValue (G : bSet B) : B :=
  ⨅ A : bSet B, ⨅ A' : bSet B, ⨅ C : bSet B, ⨅ C' : bSet B,
    imp (A ⊆ᴮ bSet.omega) (imp (A' ⊆ᴮ bSet.omega) (imp (C ⊆ᴮ bSet.omega) (imp (C' ⊆ᴮ bSet.omega)
      (imp ((bSet.pair A C ∈ᴮ G) ⊓ (bSet.pair A' C' ∈ᴮ G))
        (bitEq (actualOrdLEValue A A') (actualHarLEValue C C'))))))

noncomputable def actualIsoValue (B : Type) [NontrivialCompleteBooleanAlgebra B] : B :=
  ⨆ G : bSet B, graphPairsOnlyValue G ⊓
    (graphTotalSideValue G false ⊓ (graphTotalSideValue G true ⊓ actualPreserveReflectValue G))

@[simp] theorem bTruth_actualPreserveReflect_r213 {n : ℕ} (v : DVec (V B) n) (G : STerm n) :
    bTruth v (graphPreserveReflect_f G) = actualPreserveReflectValue (bTerm v G) := by
  simp only [graphPreserveReflect_f,bTruth_allIn_r181,bTruth_imp_r181,
    boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_biimp,equiv_bitEq_r181,
    omegaSubsets,omega,powerset,boolean_realize_bounded_term_omega',boolean_realize_bounded_term_Powerset',
    mem_powerset_subset_r181,value_f,boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    bTerm_up4_r194,bTerm_up3_r181,bTerm_up2_r181,bTerm_up_r181,bTerm_current_r181,
    bTruth_actualOrdLE_r213,Lattice.imp_infi_eq,actualPreserveReflectValue]
  let a : STerm (n+1) := x0 n
  let a' : STerm (n+2) := x0 (n+1)
  let c : STerm (n+3) := x0 (n+2)
  let c' : STerm (n+4) := x0 (n+3)
  have hGraph (A A' C C' : bSet B) :
      bTerm (DVec.cons C' (DVec.cons C (DVec.cons A' (DVec.cons A v)))) (up4 G) = bTerm v G :=
    bTerm_up4_r194 v A A' C C' G
  have hHar (A A' C C' : bSet B) :
      bTruth (DVec.cons C' (DVec.cons C (DVec.cons A' (DVec.cons A v))))
        (harmonicLE_f (up c) c') = actualHarLEValue C C' :=
    bTruth_actualHarLE_r213 _ _ _
  change (⨅ A : bSet B, ⨅ A' : bSet B, ⨅ C : bSet B, ⨅ C' : bSet B,
    imp (A ⊆ᴮ bSet.omega) (imp (A' ⊆ᴮ bSet.omega) (imp (C ⊆ᴮ bSet.omega) (imp (C' ⊆ᴮ bSet.omega)
      (imp ((bSet.pair A C ∈ᴮ bTerm (DVec.cons C' (DVec.cons C (DVec.cons A' (DVec.cons A v)))) (up4 G)) ⊓
            (bSet.pair A' C' ∈ᴮ bTerm (DVec.cons C' (DVec.cons C (DVec.cons A' (DVec.cons A v)))) (up4 G)))
        (bitEq (actualOrdLEValue A A')
          (bTruth (DVec.cons C' (DVec.cons C (DVec.cons A' (DVec.cons A v)))) (harmonicLE_f (up c) c')))))))) = _
  simp only [hGraph,hHar]

theorem bTruth_actualIso_r213 :
    boolean_realize_sentence (S := V B) densityQuotientIso_f = actualIsoValue B := by
  change bTruth (DVec.nil : DVec (V B) 0) densityQuotientIso_f = _
  simp only [densityQuotientIso_f,bTruth_sEx_r181,boolean_realize_bounded_formula_and,actualIsoValue]
  apply congrArg (fun f : bSet B → B => iSup f)
  funext G
  let u : DVec (V B) 1 := DVec.cons G DVec.nil
  let t : STerm 1 := x0 0
  have ht : bTerm u t = G := bTerm_current_r181 DVec.nil G
  change bTruth u (pairsOnly_f t) ⊓ (bTruth u (graphTotal_f t) ⊓
    (bTruth u (graphOnto_f t) ⊓ bTruth u (graphPreserveReflect_f t))) = _
  rw [bTruth_pairsOnly_r205,bTruth_graphTotal_r205,bTruth_graphOnto_r205,bTruth_actualPreserveReflect_r213,ht]

theorem bTruth_actualNonIso_r213 :
    boolean_realize_sentence (S := V B) densityQuotientNonIso_f = (actualIsoValue B)ᶜ := by
  rw [densityQuotientNonIso_f,boolean_realize_sentence_not,bTruth_actualIso_r213]

end SetLanguage
end JSP000933
