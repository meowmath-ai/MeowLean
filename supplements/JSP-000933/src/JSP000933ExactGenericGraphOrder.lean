import JSP000933GroundLogBlocksEquivalence

open Fol Lattice Erdos1123
open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

@[simp] theorem bTruth_pairsOnly_r205 {n : ℕ} (v : DVec (V β) n) (t : STerm n) :
    bTruth v (pairsOnly_f t) = graphPairsOnlyValue (bTerm v t) := by
  simp only [pairsOnly_f,bTruth_allIn_r181,bTruth_exIn_r181,bTruth_equal_r181,
    bTerm_up_r181,bTerm_up2_r181,bTerm_current_r181,boolean_realize_bounded_term_pair',
    omegaSubsets,omega,powerset,boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_Powerset',mem_powerset_subset_r181,graphPairsOnlyValue]
  rfl

@[simp] theorem bTruth_graphTotal_r205 {n : ℕ} (v : DVec (V β) n) (t : STerm n) :
    bTruth v (graphTotal_f t) = graphTotalSideValue (bTerm v t) false := by
  simp only [graphTotal_f,bTruth_allIn_r181,bTruth_exIn_r181,graphTotalSideValue,orderedPairSide,
    Bool.false_eq_true,ite_false,value_f]
  let a0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let b0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  have hPow {d : ℕ} (u : DVec (V β) d) (x : bSet β) :
      (x ∈ᴮ bTerm u omegaSubsets) = (x ⊆ᴮ bSet.omega) := by
    simp only [omegaSubsets,omega,powerset,boolean_realize_bounded_term_Powerset',
      boolean_realize_bounded_term_omega',mem_powerset_subset_r181]
  have hPair (a b : bSet β) :
      bTruth (DVec.cons b (DVec.cons a v)) (mem' (pair' (up a0) b0) (up2 t)) =
        (bSet.pair a b ∈ᴮ bTerm v t) := by
    have ht : bTerm (DVec.cons b (DVec.cons a v)) (up2 t) = bTerm v t := bTerm_up2_r181 v a b t
    refine Eq.trans ?_ (congrArg (fun z : bSet β => bSet.pair a b ∈ᴮ z) ht)
    rfl
  change (⨅ a : bSet β, imp (a ∈ᴮ bTerm v omegaSubsets)
    (⨆ b : bSet β, (b ∈ᴮ bTerm (DVec.cons a v) omegaSubsets) ⊓
      bTruth (DVec.cons b (DVec.cons a v)) (mem' (pair' (up a0) b0) (up2 t)))) = _
  simp only [hPow,hPair]

@[simp] theorem bTruth_graphOnto_r205 {n : ℕ} (v : DVec (V β) n) (t : STerm n) :
    bTruth v (graphOnto_f t) = graphTotalSideValue (bTerm v t) true := by
  simp only [graphOnto_f,bTruth_allIn_r181,bTruth_exIn_r181,graphTotalSideValue,orderedPairSide,
    ite_true,value_f]
  let a0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let b0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  have hPow {d : ℕ} (u : DVec (V β) d) (x : bSet β) :
      (x ∈ᴮ bTerm u omegaSubsets) = (x ⊆ᴮ bSet.omega) := by
    simp only [omegaSubsets,omega,powerset,boolean_realize_bounded_term_Powerset',
      boolean_realize_bounded_term_omega',mem_powerset_subset_r181]
  have hPair (a b : bSet β) :
      bTruth (DVec.cons b (DVec.cons a v)) (mem' (pair' b0 (up a0)) (up2 t)) =
        (bSet.pair b a ∈ᴮ bTerm v t) := by
    have ht : bTerm (DVec.cons b (DVec.cons a v)) (up2 t) = bTerm v t := bTerm_up2_r181 v a b t
    refine Eq.trans ?_ (congrArg (fun z : bSet β => bSet.pair b a ∈ᴮ z) ht)
    rfl
  change (⨅ a : bSet β, imp (a ∈ᴮ bTerm v omegaSubsets)
    (⨆ b : bSet β, (b ∈ᴮ bTerm (DVec.cons a v) omegaSubsets) ⊓
      bTruth (DVec.cons b (DVec.cons a v)) (mem' (pair' b0 (up a0)) (up2 t)))) = _
  simp only [hPow,hPair]

noncomputable abbrev PosB := CouplingBA ordinaryBlocks logarithmicBlocks

noncomputable def posGraph : bSet PosB := genericCouplingGraph ordinaryBlocks logarithmicBlocks

def x0 (n : ℕ) : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩

noncomputable def orderFrame_r205 (G a a' b b' : bSet PosB) : DVec (V PosB) 5 :=
  DVec.cons b' (DVec.cons b (DVec.cons a' (DVec.cons a (DVec.cons G DVec.nil))))

noncomputable def posOrd (G b b' : bSet PosB) (a a' : bSet PosB) : PosB :=
  bTruth (orderFrame_r205 G a a' b b') (ordinaryLE_f (up3 (x0 1)) (up2 (x0 2)))

noncomputable def posHar (G a a' : bSet PosB) (b b' : bSet PosB) : PosB :=
  bTruth (orderFrame_r205 G a a' b b') (harmonicLE_f (up (x0 3)) (x0 4))

theorem posOrd_ext_r205 (G b b' : bSet PosB) : BExtTwo (posOrd G b b') := by
  intro p a A c C ha hc
  unfold posOrd
  apply bTruth_vecMask_r191
  intro i
  fin_cases i <;> first | exact ha | exact hc | exact bSet.bv_refl

theorem posHar_ext_r205 (G a a' : bSet PosB) : BExtTwo (posHar G a a') := by
  intro p b B c C hb hc
  unfold posHar
  apply bTruth_vecMask_r191
  intro i
  fin_cases i <;> first | exact hb | exact hc | exact bSet.bv_refl

theorem posOrd_ground_r205 (G b b' : bSet PosB) (x y : Set ℕ) :
    posOrd G b b' (groundSubsetName PosB (fromPositive x)) (groundSubsetName PosB (fromPositive y)) =
      crispTruth PosB (ordinaryBlocks.IsNull (x \ y)) := by
  unfold posOrd
  have h₁ : bTerm (orderFrame_r205 G (groundSubsetName PosB (fromPositive x))
      (groundSubsetName PosB (fromPositive y)) b b') (up3 (x0 1)) =
        groundSubsetName PosB (fromPositive x) := by
    rfl
  have h₂ : bTerm (orderFrame_r205 G (groundSubsetName PosB (fromPositive x))
      (groundSubsetName PosB (fromPositive y)) b b') (up2 (x0 2)) =
        groundSubsetName PosB (fromPositive y) := by
    rfl
  exact (bTruth_ordinaryLE_checked_r201 _ _ _ (fromPositive x) (fromPositive y) h₁ h₂).trans
    (crispTruth_propext_r188 (ordinaryIntegerNull_blocks_iff_r203 x y))

theorem posHar_ground_r205 (G a a' : bSet PosB) (x y : Set ℕ) :
    posHar G a a' (groundSubsetName PosB (fromPositive x)) (groundSubsetName PosB (fromPositive y)) =
      crispTruth PosB (logarithmicBlocks.IsNull (x \ y)) := by
  unfold posHar
  have h₁ : bTerm (orderFrame_r205 G a a' (groundSubsetName PosB (fromPositive x))
      (groundSubsetName PosB (fromPositive y))) (up (x0 3)) =
        groundSubsetName PosB (fromPositive x) := by
    rfl
  have h₂ : bTerm (orderFrame_r205 G a a' (groundSubsetName PosB (fromPositive x))
      (groundSubsetName PosB (fromPositive y))) (x0 4) =
        groundSubsetName PosB (fromPositive y) := by
    rfl
  exact (bTruth_harmonicLE_checked_r201 _ _ _ (fromPositive x) (fromPositive y) h₁ h₂).trans
    (crispTruth_propext_r188 (harmonicIntegerNull_blocks_iff_r204 x y))

theorem generic_graph_preserveReflect_r205 :
    (⊤ : PosB) ≤ bTruth (DVec.cons posGraph DVec.nil) (graphPreserveReflect_f (x0 0)) := by
  simp only [graphPreserveReflect_f,bTruth_allIn_r181,bTruth_imp_r181,
    boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_biimp,equiv_bitEq_r181,
    omegaSubsets,omega,powerset,boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_Powerset',mem_powerset_subset_r181,value_f,
    boolean_realize_bounded_formula_mem',boolean_realize_bounded_term_pair',
    bTerm_up4_r194,bTerm_up3_r181,bTerm_up2_r181,bTerm_up_r181,x0,bTerm_current_r181,
    Lattice.imp_infi_eq]
  apply le_iInf
  intro A
  apply le_iInf
  intro A'
  apply le_iInf
  intro B
  apply le_iInf
  intro B'
  rw [← _root_.deduction,← _root_.deduction,← _root_.deduction,← _root_.deduction]
  have h := generic_graph_orderOfCanonical_arithmetic_r188
    (posOrd posGraph B B') (posHar posGraph A A') (posOrd_ext_r205 posGraph B B')
    (posHar_ext_r205 posGraph A A') (posOrd_ground_r205 posGraph B B') (posHar_ground_r205 posGraph A A')
  have hv : (⊤ : PosB) ≤ imp ((bSet.pair A B ∈ᴮ posGraph) ⊓ (bSet.pair A' B' ∈ᴮ posGraph))
      (bitEq (posOrd posGraph B B' A A') (posHar posGraph A A' B B')) :=
    h.trans ((iInf_le _ A).trans ((iInf_le _ A').trans ((iInf_le _ B).trans (iInf_le _ B'))))
  exact le_top.trans hv

end SetLanguage
end JSP000933
