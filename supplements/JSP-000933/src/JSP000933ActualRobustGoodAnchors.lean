import JSP000933ActualAnchoredGapTests
import Mathlib.Order.SymmDiff

open scoped Flypitch symmDiff

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameBudgetValue_scale_antitone_r316 (h : Bool) (A C : ℕ → B) (n : ℕ)
    {k K : ℕ} (hk : k≤K) :
    nameBudgetValue h (realBitsName A) (realBitsName C) K n≤
      nameBudgetValue h (realBitsName A) (realBitsName C) k n := by
  let E : BudgetExpr (Fin 4) := ⟨h,.var 0,.var 1,K⟩
  let R : BudgetExpr (Fin 4) := ⟨h,.var 0,.var 1,k⟩
  have hG (X : Fin 4 → Set ℕ) : E.groundHolds X n → R.groundHolds X n := by
    change GroundBudgetHolds h ((.var 0 : SetBitExpr (Fin 4)).groundSet X)
      ((.var 1 : SetBitExpr (Fin 4)).groundSet X) K n →
      GroundBudgetHolds h ((.var 0 : SetBitExpr (Fin 4)).groundSet X)
        ((.var 1 : SetBitExpr (Fin 4)).groundSet X) k n
    rw [groundBudgetHolds_weighted_r232,groundBudgetHolds_weighted_r232]
    intro h
    exact (Nat.mul_le_mul_right _ hk).trans h
  have hh := finite_budget_unary_r233 E R (nameFour A C A C) n hG
  simpa [E,R,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.evalB,nameFour,
    membershipBits_realBitsName_r128] using hh

theorem eventuallySmallError_scale_antitone_r316 (h : Bool) (a b : ℕ → B)
    {k K : ℕ} (hk : k≤K) : eventuallySmallError h K a b≤eventuallySmallError h k a b := by
  unfold eventuallySmallError eventualBudgetAt
  apply iSup_le
  intro N
  apply le_iSup_of_le N
  apply budgetTail_of_forall_r229
  intro n hn
  exact (budgetTail_apply_r229 _ K N n hn).trans
    (nameBudgetValue_scale_antitone_r316 h (bitsSymmDiff a b) (fun _ => ⊥) n hk)

theorem bitsSymmDiff_comm_r316 (a b : ℕ → B) : bitsSymmDiff a b=bitsSymmDiff b a := by
  funext m
  simpa only [bitsSymmDiff_at_r298] using symmDiff_comm (a m) (b m)

theorem nameErrorBudget_comm_r316 (h : Bool) (k n : ℕ) (a b : ℕ → B) :
    nameErrorBudget h k n a b=nameErrorBudget h k n b a :=
  congrArg (fun x => nameBudgetValue h (realBitsName x) (realBitsName (fun _ => ⊥)) k n)
    (bitsSymmDiff_comm_r316 a b)

theorem robustGoodTail_anchorCover_r316 {p : B} {H : (ℕ → B) → (ℕ → B) → ℕ → B}
    (hH : NamedTwoArgContinuous p H) (R : (ℕ → B) → ℕ → B)
    (k : ℕ) (x : ℕ → B) (hGood : p≤robustGoodTails (goodTailCodesAt H R (4*k) x)) :
    p≤⨆ Nu : ℕ × Word, anchorGapClosedValue H (2*k) Nu.2 Nu.1 x := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  let C := goodTailCodesAt H R (4*k) x
  have hI : q≤goodTailInteriorValue C [] := hqp.trans (hGood.trans (iInf_le _ []))
  obtain ⟨N,r,hr,hrq,hR0⟩ := exists_nonzero_below_choice_r135 q hq
    (fun N => ⨆ u : {u : Word // ExtendsWord [] u}, cylinderInClosedValue (C N) u.val) hI
  obtain ⟨u,t,ht,htr,hIu⟩ := exists_nonzero_below_choice_r135 r hr
    (fun u : {u : Word // ExtendsWord [] u} => cylinderInClosedValue (C N) u.val) hR0
  refine ⟨t,ht,htr.trans hrq,le_iSup_of_le (N,u.val) ?_⟩
  unfold anchorGapClosedValue
  apply le_iInf
  intro y
  apply (le_materialImp_iff_r126 _ _ _).mpr
  let b := paddedWordBits (B := B) u.val
  let s := t⊓cylinderValue y u.val
  have hsP : s≤p := inf_le_left.trans (htr.trans (hrq.trans hqp))
  have hy := goodTailInterior_true_r315 hH R (4*k) N u.val x y hsP (inf_le_left.trans hIu) inf_le_right
  have hb := goodTailInterior_true_r315 hH R (4*k) N u.val x b hsP (inf_le_left.trans hIu)
    (le_top.trans (paddedWord_in_ownCylinder_r280 u.val))
  apply budgetTail_of_forall_r229
  intro n hn
  have hy' := hy.trans (budgetTail_apply_r229 _ (4*k) N n hn)
  have hb' : s≤nameErrorBudget true (4*k) n (R x) (H x b) :=
    (hb.trans (budgetTail_apply_r229 _ (4*k) N n hn)).trans_eq (nameErrorBudget_comm_r316 _ _ _ _ _)
  have hTri := nameErrorBudget_triangle_r289 true (H x y) (R x) (H x b) (2*k) n
  rw [show 2*(2*k)=4*k by omega] at hTri
  exact (le_inf hy' hb').trans hTri

theorem robustGoodTail_anchorGood_r316 {p q : B} {H : (ℕ → B) → (ℕ → B) → ℕ → B}
    (hH : NamedTwoArgContinuous p H) (R : (ℕ → B) → ℕ → B)
    (k N : ℕ) (u : Word) (x : ℕ → B) (hqp : q≤p)
    (hGood : q≤robustGoodTails (goodTailCodesAt H R (4*k) x))
    (hGap : q≤anchorGapClosedValue H (2*k) u N x) :
    q≤eventuallySmallError true k (H x (paddedWordBits u)) (R x) := by
  apply le_of_dense_named_refinements_r219
  intro r hr hrq
  let C := goodTailCodesAt H R (4*k) x
  have hI : r≤goodTailInteriorValue C u := hrq.trans (hGood.trans (iInf_le _ u))
  obtain ⟨M,s,hs,hsr,hS⟩ := exists_nonzero_below_choice_r135 r hr
    (fun M => ⨆ v : {v : Word // ExtendsWord u v}, cylinderInClosedValue (C M) v.val) hI
  obtain ⟨v,t,ht,hts,hT⟩ := exists_nonzero_below_choice_r135 s hs
    (fun v : {v : Word // ExtendsWord u v} => cylinderInClosedValue (C M) v.val) hS
  let y := paddedWordBits (B := B) v.val
  let b := paddedWordBits (B := B) u
  have htr := hts.trans hsr
  have htv : t≤cylinderValue y v.val := le_top.trans (paddedWord_in_ownCylinder_r280 v.val)
  have htu : t≤cylinderValue y u := htv.trans (cylinderWord_mono_r173 y v.property)
  have hGY := goodTailInterior_true_r315 hH R (4*k) M v.val x y (htr.trans (hrq.trans hqp)) hT htv
  have hGB := anchorGapClosed_apply_r315 H (2*k) N u x y (htr.trans (hrq.trans hGap)) htu
  have hL : t≤eventuallySmallError true (2*k) (H x b) (H x y) := by
    unfold eventuallySmallError eventualBudgetAt
    apply le_iSup_of_le N
    apply budgetTail_of_forall_r229
    intro n hn
    exact (hGB.trans (budgetTail_apply_r229 _ (2*k) N n hn)).trans_eq
      (nameErrorBudget_comm_r316 _ _ _ _ _)
  have hR : t≤eventuallySmallError true (2*k) (H x y) (R x) :=
    (le_iSup_of_le M hGY).trans (eventuallySmallError_scale_antitone_r316 _ _ _ (show 2*k≤4*k by omega))
  exact ⟨t,ht,htr,(le_inf hL hR).trans (eventuallySmallError_triangle_r290 true k _ _ _)⟩

end SetLanguage
end JSP000933
