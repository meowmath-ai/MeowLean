import JSP000933LiveBudgetComplementExtrema

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem mixedEventual_mono_r235 (T S : ℕ → ℕ → B) (h : ∀ k n, T k n ≤ S k n) :
    mixedEventualBudgetValue T ≤ mixedEventualBudgetValue S := by
  apply le_iInf
  intro k
  apply (iInf_le _ k).trans
  apply sup_le_sup le_rfl
  apply iSup_le
  intro N
  apply le_iSup_of_le N
  apply le_iInf
  intro n
  exact (iInf_le _ n).trans (sup_le_sup le_rfl (h k n))

theorem mixedEventual_of_positiveTails_r235 (T : ℕ → ℕ → B) (p : B)
    (h : ∀ k, k≠0 → p ≤ ⨆ N, budgetTail T k N) : p ≤ mixedEventualBudgetValue T := by
  classical
  apply le_iInf
  intro k
  by_cases hk : k=0
  · simp [crispTruth,_root_.imp,hk]
  · change p ≤ imp (crispTruth B (k ≠ 0)) (⨆ N : ℕ, budgetTail T k N)
    have he : crispTruth B (k ≠ 0) = ⊤ := by simp [crispTruth,hk]
    rw [he]
    exact (h k hk).trans_eq (by simp [_root_.imp])

theorem mixedEventual_positiveTails_r235 (T : ℕ → ℕ → B) (k : ℕ) (hk : k≠0) :
    mixedEventualBudgetValue T ≤ ⨆ N, budgetTail T k N := by
  classical
  have hh : mixedEventualBudgetValue T ≤ imp (crispTruth B (k≠0))
      (⨆ N, budgetTail T k N) := iInf_le _ k
  simpa [crispTruth,_root_.imp,hk] using hh

theorem mixedEventual_binary_r235 (T S R : ℕ → ℕ → B)
    (h : ∀ k n, T (2*k) n ⊓ S (2*k) n ≤ R k n) :
    mixedEventualBudgetValue T ⊓ mixedEventualBudgetValue S ≤ mixedEventualBudgetValue R := by
  apply mixedEventual_of_positiveTails_r235
  intro k hk
  have h2 : 2*k≠0 := by omega
  apply (inf_le_inf (mixedEventual_positiveTails_r235 T (2*k) h2)
    (mixedEventual_positiveTails_r235 S (2*k) h2)).trans
  rw [iSup_inf_iSup]
  apply iSup_le
  intro ab
  apply le_iSup_of_le (max ab.1 ab.2)
  apply budgetTail_of_forall_r229
  intro n hn
  exact (inf_le_inf
    (budgetTail_apply_r229 T (2*k) ab.1 n ((le_max_left _ _).trans hn))
    (budgetTail_apply_r229 S (2*k) ab.2 n ((le_max_right _ _).trans hn))).trans (h k n)

noncomputable def liveLE (h : Bool) (x y : ℕ → B) : B :=
  nameOrderValue h (realBitsName x) (realBitsName y)

theorem liveLE_meet_right_r235 (h : Bool) (x y z : ℕ → B) :
    liveLE h x (bitsMeet y z) = liveLE h x y ⊓ liveLE h x z := by
  apply le_antisymm
  · exact le_inf (mixedEventual_mono_r235 _ _ (fun k n =>
      (nameBudgetValue_meet_right_elim_r233 h x y z k n).trans inf_le_left))
      (mixedEventual_mono_r235 _ _ (fun k n =>
      (nameBudgetValue_meet_right_elim_r233 h x y z k n).trans inf_le_right))
  · exact mixedEventual_binary_r235 _ _ _ (nameBudgetValue_meet_right_r233 h x y z)

theorem liveLE_compl_reverse_r235 (h : Bool) (x y : ℕ → B) :
    liveLE h (bitsComplement y) (bitsComplement x) = liveLE h x y := by
  unfold liveLE nameOrderValue
  exact congrArg mixedEventualBudgetValue (funext (fun k => funext (fun n =>
    nameBudgetValue_compl_reverse_r234 h x y k n)))

theorem liveLE_join_left_r235 (h : Bool) (x y z : ℕ → B) :
    liveLE h (bitsJoin x y) z = liveLE h x z ⊓ liveLE h y z := by
  calc
    _ = liveLE h (bitsComplement z) (bitsComplement (bitsJoin x y)) :=
      (liveLE_compl_reverse_r235 h _ _).symm
    _ = liveLE h (bitsComplement z) (bitsMeet (bitsComplement x) (bitsComplement y)) := by
      rw [bitsJoin_deMorgan_r234,bitsComplement_compl_r234]
    _ = _ := by rw [liveLE_meet_right_r235,liveLE_compl_reverse_r235,liveLE_compl_reverse_r235]

theorem liveLE_bot_r235 (h : Bool) (x : ℕ → B) : (⊤ : B) ≤ liveLE h (fun _ => ⊥) x := by
  apply nameOrder_of_positiveTails_r229
  intro k _
  apply le_iSup_of_le 0
  exact budgetTail_of_forall_r229 _ k 0 ⊤ (fun n _ => nameBudgetValue_bot_r234 h x k n)

theorem liveLE_top_r235 (h : Bool) (x : ℕ → B) : (⊤ : B) ≤ liveLE h x (fun _ => ⊤) := by
  apply nameOrder_of_positiveTails_r229
  intro k _
  apply le_iSup_of_le 0
  exact budgetTail_of_forall_r229 _ k 0 ⊤ (fun n _ => nameBudgetValue_top_r234 h x k n)

end SetLanguage
end JSP000933
