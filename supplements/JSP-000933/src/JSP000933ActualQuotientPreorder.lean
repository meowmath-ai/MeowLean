import JSP000933MixedQuotientBudgetTriangle

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def budgetTail (T : ℕ → ℕ → B) (k N : ℕ) : B :=
  ⨅ n : ℕ, imp (crispTruth B (N≤n)) (T k n)

noncomputable def nameOrderValue (h : Bool) (A C : bSet B) : B :=
  mixedEventualBudgetValue (nameBudgetValue h A C)

theorem budgetTail_of_forall_r229 (T : ℕ → ℕ → B) (k N : ℕ) (p : B)
    (h : ∀ n ≥ N, p ≤ T k n) : p ≤ budgetTail T k N := by
  classical
  apply le_iInf
  intro n
  by_cases hn : N≤n
  · simpa [crispTruth,_root_.imp,hn] using h n hn
  · simp [crispTruth,_root_.imp,hn]

theorem budgetTail_apply_r229 (T : ℕ → ℕ → B) (k N n : ℕ) (hn : N≤n) :
    budgetTail T k N ≤ T k n := by
  classical
  have h : budgetTail T k N ≤ imp (crispTruth B (N ≤ n)) (T k n) :=
    iInf_le (fun j : ℕ => imp (crispTruth B (N ≤ j)) (T k j)) n
  have he : imp (crispTruth B (N ≤ n)) (T k n) = T k n := by
    simp [crispTruth,_root_.imp,hn]
  exact h.trans_eq he

theorem nameOrder_of_positiveTails_r229 (h : Bool) (A C : bSet B) (p : B)
    (hT : ∀ k : ℕ, k≠0 → p ≤ ⨆ N : ℕ, budgetTail (nameBudgetValue h A C) k N) :
    p ≤ nameOrderValue h A C := by
  classical
  apply le_iInf
  intro k
  by_cases hk : k=0
  · simp [crispTruth,_root_.imp,hk]
  · change p ≤ imp (crispTruth B (k ≠ 0)) (⨆ N : ℕ, budgetTail (nameBudgetValue h A C) k N)
    have he : crispTruth B (k ≠ 0) = ⊤ := by simp [crispTruth,hk]
    rw [he]
    exact (hT k hk).trans_eq (by simp [_root_.imp])

theorem nameOrder_positiveTails_r229 (h : Bool) (A C : bSet B) (k : ℕ) (hk : k≠0) :
    nameOrderValue h A C ≤ ⨆ N : ℕ, budgetTail (nameBudgetValue h A C) k N := by
  classical
  have hh : nameOrderValue h A C ≤ imp (crispTruth B (k≠0))
      (⨆ N : ℕ, budgetTail (nameBudgetValue h A C) k N) := iInf_le _ k
  simpa [crispTruth,_root_.imp,hk] using hh

theorem nameOrderValue_refl_r229 (h : Bool) (A : bSet B) :
    (⊤ : B) ≤ nameOrderValue h A A := by
  apply nameOrder_of_positiveTails_r229
  intro k _
  apply le_iSup_of_le 0
  exact budgetTail_of_forall_r229 _ k 0 ⊤ (fun n _ => nameBudgetValue_refl_r228 h A k n)

theorem nameOrderValue_trans_r229 (h : Bool) (A M C : bSet B) :
    nameOrderValue h A M ⊓ nameOrderValue h M C ≤ nameOrderValue h A C := by
  apply nameOrder_of_positiveTails_r229
  intro k hk
  have h2 : 2*k ≠ 0 := by omega
  apply (inf_le_inf (nameOrder_positiveTails_r229 h A M (2*k) h2)
    (nameOrder_positiveTails_r229 h M C (2*k) h2)).trans
  rw [iSup_inf_iSup]
  apply iSup_le
  intro sz
  apply le_iSup_of_le (max sz.1 sz.2)
  apply budgetTail_of_forall_r229
  intro n hn
  have h₁ : sz.1 ≤ n := (le_max_left _ _).trans hn
  have h₂ : sz.2 ≤ n := (le_max_right _ _).trans hn
  exact (inf_le_inf (budgetTail_apply_r229 _ _ _ n h₁) (budgetTail_apply_r229 _ _ _ n h₂)).trans
    (nameBudgetValue_triangle_r228 h A M C k n)

@[simp] theorem nameOrder_false_r229 (A C : bSet B) :
    nameOrderValue false A C = actualOrdLEValue A C := rfl

@[simp] theorem nameOrder_true_r229 (A C : bSet B) :
    nameOrderValue true A C = actualHarLEValue A C := rfl

theorem actualIso_selected_inverseOrd_r229 (p : B) (G : bSet B)
    (F R : (ℕ → B) → ℕ → B) (hG : p ≤ actualPreserveReflectValue G)
    (hF : ∀ x, p ≤ graphPairBits G false x (F x)) (hR : ∀ y, p ≤ graphPairBits G true y (R y))
    (x : ℕ → B) :
    p ≤ actualOrdLEValue (realBitsName x) (realBitsName (R (F x))) ⊓
      actualOrdLEValue (realBitsName (R (F x))) (realBitsName x) := by
  let a := realBitsName x
  let b := realBitsName (R (F x))
  let c := realBitsName (F x)
  have hg : p ≤ graphPairBits G false (R (F x)) (F x) := hR (F x)
  have h₁ := graph_orderOnSelectedNames_r214 G p hG x (R (F x)) (F x) (F x) (hF x) hg
  have h₂ := graph_orderOnSelectedNames_r214 G p hG (R (F x)) x (F x) (F x) hg (hF x)
  have he : actualHarLEValue c c = (⊤ : B) := top_unique (nameOrderValue_refl_r229 true c)
  have hh (u : B) (h : p ≤ bitEq u (actualHarLEValue c c)) : p ≤ u := by
    rw [he] at h
    exact (le_inf le_rfl le_top).trans
      (((le_bitEq_iff_r126 p u ⊤).mp h).ge.trans inf_le_right)
  exact le_inf (hh _ h₁) (hh _ h₂)

end SetLanguage
end JSP000933
