import JSP000933BooleanBoundedNaturals

open Fol Lattice
open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open CantorCodes BooleanNames PositiveForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

@[simp] theorem bTruth_allOmega_r192 {n : ℕ} (v : DVec (V B) n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn omega φ) = ⨅ i : ℕ,
      bTruth (DVec.cons (bSet.of_nat i) v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) :=
  bTruth_boundedForallOmega_r191 v omega rfl φ

@[simp] theorem bTruth_exOmega_r192 {n : ℕ} (v : DVec (V B) n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (exIn omega φ) = ⨆ i : ℕ,
      bTruth (DVec.cons (bSet.of_nat i) v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) :=
  bTruth_boundedExistsOmega_r191 v omega rfl φ

@[simp] theorem bTerm_zero_checked_r192 {n : ℕ} (v : DVec (V B) n) :
    bTerm v zero = (bSet.of_nat 0 : bSet B) := by
  change (∅ : bSet B) = bSet.check (PSet.ofNat 0)
  rw [show PSet.ofNat 0 = (∅ : PSet) from rfl,bSet.check_empty_eq_empty]

theorem memberCheckedNat_succ_r192 (x : bSet B) (n : ℕ) :
    (x ∈ᴮ bSet.of_nat (n+1)) = (x ∈ᴮ bSet.of_nat n) ⊔ (x =ᴮ bSet.of_nat n) := by
  rw [memberCheckedNat_cases_r174 (n+1),memberCheckedNat_cases_r174 n]
  apply le_antisymm
  · apply iSup_le
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact (le_iSup (fun k : Fin n => x =ᴮ bSet.of_nat k.val) j).trans le_sup_left
  · apply sup_le
    · apply iSup_le
      intro j
      exact le_iSup (fun k : Fin (n+1) => x =ᴮ bSet.of_nat k.val) j.castSucc
    · exact le_iSup (fun k : Fin (n+1) => x =ᴮ bSet.of_nat k.val) (Fin.last n)

theorem bv_eq_iInf_membershipBitEq_r192 (x y : bSet B) :
    (x =ᴮ y) = ⨅ z : bSet B, bitEq (z ∈ᴮ x) (z ∈ᴮ y) := by
  rw [bSet.bv_eq_unfold']
  apply le_antisymm
  · apply le_iInf
    intro z
    exact le_inf (inf_le_left.trans (iInf_le _ z)) (inf_le_right.trans (iInf_le _ z))
  · refine le_inf (le_iInf (fun z => ?_)) (le_iInf (fun z => ?_))
    · exact (iInf_le (fun z : bSet B => bitEq (z ∈ᴮ x) (z ∈ᴮ y)) z).trans inf_le_left
    · exact (iInf_le (fun z : bSet B => bitEq (z ∈ᴮ x) (z ∈ᴮ y)) z).trans inf_le_right

theorem bTruth_successor_checked_r192 {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (i : ℕ) (ha : bTerm v a = bSet.of_nat i) :
    bTruth v (successor_f a b) = (bTerm v b =ᴮ bSet.of_nat (i+1)) := by
  rw [bv_eq_iInf_membershipBitEq_r192 (bTerm v b) (bSet.of_nat (i+1))]
  simp only [successor_f,bTruth_sAll_r181,boolean_realize_bounded_formula_biimp,
    boolean_realize_bounded_formula_or,equiv_bitEq_r181]
  apply congrArg (fun f : bSet B → B => iInf f)
  funext x
  let w : DVec (V B) (n+1) := DVec.cons x v
  let z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  change bitEq (bTerm w z ∈ᴮ bTerm w (up b))
    ((bTerm w z ∈ᴮ bTerm w (up a)) ⊔ (bTerm w z =ᴮ bTerm w (up a))) = _
  have hz : bTerm w z = x := bTerm_current_r181 v x
  have hA : bTerm w (up a) = bSet.of_nat i := (bTerm_up_r181 v x a).trans ha
  have hB : bTerm w (up b) = bTerm v b := bTerm_up_r181 v x b
  rw [hz,hA,hB,memberCheckedNat_succ_r192]

theorem bTruth_successor_twoChecked_r192 {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (i j : ℕ) (ha : bTerm v a = bSet.of_nat i) (hb : bTerm v b = bSet.of_nat j) :
    bTruth v (successor_f a b) = crispTruth B (j = i+1) := by
  rw [bTruth_successor_checked_r192 v a b i ha,hb,checkedNat_eq_crisp_r189]

theorem bTruth_natLE_checked_r192 {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (i j : ℕ) (ha : bTerm v a = bSet.of_nat i) (hb : bTerm v b = bSet.of_nat j) :
    bTruth v (natLE_f a b) = crispTruth B (i ≤ j) := by
  classical
  simp only [natLE_f,boolean_realize_bounded_formula_or,boolean_realize_bounded_formula_mem',
    bTruth_equal_r181,ha,hb,checkedNat_mem_r174,checkedNat_eq_crisp_r189]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h,h.le,crispTruth]
  · simp [crispTruth]
  · have hlt : ¬ i < j := not_lt_of_ge h.le
    have hle : ¬ i ≤ j := not_le_of_gt h
    have hne : i ≠ j := ne_of_gt h
    simp [hlt,hle,hne,crispTruth]

theorem iSup_crisp_r192 {I : Type*} (P : I → Prop) :
    (⨆ i, crispTruth B (P i)) = crispTruth B (∃ i, P i) := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i,hi⟩ := h
    have hh : (⊤ : B) ≤ ⨆ j, crispTruth B (P j) :=
      (show crispTruth B (P i) = ⊤ by simp [crispTruth,hi]).ge.trans (le_iSup (fun j => crispTruth B (P j)) i)
    exact (top_unique hh).trans (by simp [crispTruth,show ∃ j, P j from ⟨i,hi⟩])
  · apply le_antisymm
    · apply iSup_le
      intro i
      simp [crispTruth,h,show ¬ P i from fun hi => h ⟨i,hi⟩]
    · simp [crispTruth,h]

theorem iInf_crisp_r192 {I : Type*} (P : I → Prop) :
    (⨅ i, crispTruth B (P i)) = crispTruth B (∀ i, P i) := by
  classical
  by_cases h : ∀ i, P i
  · apply le_antisymm
    · simp [crispTruth,h]
    · apply le_iInf
      intro i
      simp [crispTruth,h,h i]
  · have hi : ∃ i, ¬ P i := not_forall.mp h
    obtain ⟨i,hi⟩ := hi
    apply le_antisymm
    · apply (iInf_le (fun j => crispTruth B (P j)) i).trans
      simp [crispTruth,hi,h]
    · simp [crispTruth,h]

end SetLanguage
end JSP000933
