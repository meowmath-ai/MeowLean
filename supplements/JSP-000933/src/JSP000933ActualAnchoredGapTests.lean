import JSP000933ActualLargeUniformCapValues

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def NamedTwoArgContinuous (p : B) (H : (ℕ → B) → (ℕ → B) → ℕ → B) : Prop :=
  (∀ t, NamedContinuousOn p (fun x => H x t)) ∧ (∀ x, NamedContinuousOn p (H x))

noncomputable def goodTailCodesAt (H : (ℕ → B) → (ℕ → B) → ℕ → B)
    (R : (ℕ → B) → ℕ → B) (k : ℕ) (x : ℕ → B) : ℕ → Word → B :=
  fun N => actualErrorTailBadCode (H x) (fun _ => R x) true k N

noncomputable def anchorGapClosedValue (H : (ℕ → B) → (ℕ → B) → ℕ → B)
    (k : ℕ) (u : Word) (N : ℕ) (x : ℕ → B) : B :=
  ⨅ t : ℕ → B, imp (cylinderValue t u)
    (budgetTail (fun k n => nameErrorBudget true k n (H x t) (H x (paddedWordBits u))) k N)

noncomputable def anchorGapBadCode (H : (ℕ → B) → (ℕ → B) → ℕ → B)
    (k : ℕ) (u : Word) (N : ℕ) (s : Word) : B :=
  ⨆ t : ℕ → B, cylinderValue t u⊓
    actualErrorTailBadCode (fun x => H x t) (fun x => H x (paddedWordBits u)) true k N s

theorem openValue_const_inf_r315 (a : B) (K : Word → B) (x : ℕ → B) :
    openValue (fun u => a⊓K u) x=a⊓openValue K x := by
  unfold openValue
  rw [inf_iSup_eq]
  simp only [inf_assoc]

theorem anchorGapBadCode_mask_r315 {p : B} {H : (ℕ → B) → (ℕ → B) → ℕ → B}
    (hH : NamedTwoArgContinuous p H) (k N : ℕ) (u : Word) (x : ℕ → B) :
    p⊓openValue (anchorGapBadCode H k u N) x=p⊓(anchorGapClosedValue H k u N x)ᶜ := by
  unfold anchorGapBadCode anchorGapClosedValue
  rw [openValue_iSup_code_r274,compl_iInf]
  simp only [openValue_const_inf_r315,_root_.imp,compl_sup,compl_compl,inf_iSup_eq]
  exact congrArg iSup (funext (fun t => mask_inf_congr_r126 rfl
    (actualErrorTailBadCode_mask_r302 (hH.1 t) (hH.1 (paddedWordBits u)) true k N x)))

theorem goodTailInterior_true_r315 {p : B} {H : (ℕ → B) → (ℕ → B) → ℕ → B}
    (hH : NamedTwoArgContinuous p H) (R : (ℕ → B) → ℕ → B)
    (k N : ℕ) (u : Word) (x t : ℕ → B) {q : B}
    (hq : q≤p) (hI : q≤cylinderInClosedValue (goodTailCodesAt H R k x N) u)
    (hT : q≤cylinderValue t u) :
    q≤budgetTail (fun k n => nameErrorBudget true k n (H x t) (R x)) k N := by
  have hC := cylinderInClosedValue_elim_r280 (goodTailCodesAt H R k x N) u t hI hT
  have hE := mask_compl_congr_r126 (mask_under_r302 hq
    (actualErrorTailBadCode_mask_r302 (hH.2 x) (namedConstant_continuous_r302 p (R x)) true k N t))
  rw [compl_compl] at hE
  exact ((le_inf le_rfl hC).trans_eq hE).trans inf_le_right

theorem anchorGapClosed_apply_r315 (H : (ℕ → B) → (ℕ → B) → ℕ → B)
    (k N : ℕ) (u : Word) (x t : ℕ → B) {p : B}
    (h : p≤anchorGapClosedValue H k u N x) (hT : p≤cylinderValue t u) :
    p≤budgetTail (fun k n => nameErrorBudget true k n (H x t) (H x (paddedWordBits u))) k N :=
  _root_.context_imp_elim (h.trans (iInf_le _ t)) hT

end SetLanguage
end JSP000933
