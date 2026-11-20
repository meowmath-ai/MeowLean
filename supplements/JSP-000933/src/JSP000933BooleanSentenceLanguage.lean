import JSP000933SetSentence
import JSP000933BooleanRealEquality

open Fol Lattice
open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable abbrev bTerm {n : ℕ} (v : DVec (V B) n) (t : STerm n) : bSet B :=
  boolean_realize_bounded_term v t DVec.nil

noncomputable abbrev bTruth {n : ℕ} (v : DVec (V B) n) (φ : SForm n) : B :=
  boolean_realize_bounded_formula v φ DVec.nil

@[simp] theorem bTerm_current_r181 {n : ℕ} (v : DVec (V B) n) (x : V B) :
    bTerm (DVec.cons x v) (bd_var ⟨0,Nat.succ_pos n⟩) = x := rfl

@[simp] theorem bTerm_up_r181 {n : ℕ} (v : DVec (V B) n) (x : V B) (t : STerm n) :
    bTerm (DVec.cons x v) (up t) = bTerm v t :=
  boolean_realize_bounded_term_subst_lift v x t DVec.nil

private theorem lift_successor_eq_r181 {n l : ℕ}
    (t : bounded_preterm L_ZFC n l) (k : ℕ) :
    lift_bounded_term t (k+1) = lift_bounded_term (lift_bounded_term t k) 1 := by
  induction t with
  | bd_var i => simp [lift_bounded_term,Nat.add_assoc]
  | bd_func _ => rfl
  | bd_app a b ha hb =>
    simp only [lift_bounded_term,lift_bounded_term_at] at ha hb ⊢
    rw [ha,hb]

@[simp] theorem bTerm_up2_r181 {n : ℕ} (v : DVec (V B) n) (x y : V B) (t : STerm n) :
    bTerm (DVec.cons y (DVec.cons x v)) (up2 t) = bTerm v t := by
  have h : up2 t = up (up t) := lift_successor_eq_r181 t 1
  rw [h,bTerm_up_r181,bTerm_up_r181]

@[simp] theorem bTerm_up3_r181 {n : ℕ} (v : DVec (V B) n) (x y z : V B) (t : STerm n) :
    bTerm (DVec.cons z (DVec.cons y (DVec.cons x v))) (up3 t) = bTerm v t := by
  have h : up3 t = up (up2 t) := lift_successor_eq_r181 t 2
  rw [h,bTerm_up_r181,bTerm_up2_r181]

@[simp] theorem bTruth_equal_r181 {n : ℕ} (v : DVec (V B) n) (t s : STerm n) :
    bTruth v (bd_equal t s) = (bTerm v t =ᴮ bTerm v s) := rfl

@[simp] theorem bTruth_imp_r181 {n : ℕ} (v : DVec (V B) n) (φ ψ : SForm n) :
    bTruth v (bd_imp φ ψ) = imp (bTruth v φ) (bTruth v ψ) := rfl

@[simp] theorem bTruth_sAll_r181 {n : ℕ} (v : DVec (V B) n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (sAll φ) = ⨅ x : bSet B,
      bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := rfl

@[simp] theorem bTruth_sEx_r181 {n : ℕ} (v : DVec (V B) n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (sEx φ) = ⨆ x : bSet B,
      bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) :=
  boolean_realize_bounded_formula_ex

private theorem bTruth_mem_r181 {n : ℕ} (v : DVec (V B) n) (s t : STerm n) :
    bTruth v (mem' s t) = (bTerm v s ∈ᴮ bTerm v t) :=
  boolean_realize_bounded_formula_mem' s t

private theorem bTruth_and_r181 {n : ℕ} (v : DVec (V B) n) (φ ψ : SForm n) :
    bTruth v (bd_and φ ψ) = bTruth v φ ⊓ bTruth v ψ :=
  boolean_realize_bounded_formula_and

@[simp] theorem bTruth_allIn_r181 {n : ℕ} (v : DVec (V B) n) (t : STerm n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn t φ) = ⨅ x : bSet B, imp (x ∈ᴮ bTerm v t)
      (bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩))) := by
  simp only [allIn,bTruth_sAll_r181,bTruth_imp_r181]
  apply congrArg (fun f : bSet B → B => iInf f)
  funext x
  let w : DVec (V B) (n+1) := DVec.cons x v
  let s : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hs : bTerm w s = x := bTerm_current_r181 v x
  have ht : bTerm w (up t) = bTerm v t := bTerm_up_r181 v x t
  have h := (bTruth_mem_r181 w s (up t)).trans (congrArg₂ (fun a b : bSet B => a ∈ᴮ b) hs ht)
  exact congrArg (fun b => imp b (bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)))) h

@[simp] theorem bTruth_exIn_r181 {n : ℕ} (v : DVec (V B) n) (t : STerm n)
    (φ : STerm (n+1) → SForm (n+1)) :
    bTruth v (exIn t φ) = ⨆ x : bSet B, (x ∈ᴮ bTerm v t) ⊓
      bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  simp only [exIn,bTruth_sEx_r181,bTruth_and_r181]
  apply congrArg (fun f : bSet B → B => iSup f)
  funext x
  let w : DVec (V B) (n+1) := DVec.cons x v
  let s : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hs : bTerm w s = x := bTerm_current_r181 v x
  have ht : bTerm w (up t) = bTerm v t := bTerm_up_r181 v x t
  have h := (bTruth_mem_r181 w s (up t)).trans (congrArg₂ (fun a b : bSet B => a ∈ᴮ b) hs ht)
  exact congrArg (fun b => b ⊓ bTruth (DVec.cons x v) (φ (bd_var ⟨0,Nat.succ_pos n⟩))) h

theorem equiv_bitEq_r181 (a b : B) : bihimp a b = bitEq a b := by
  simp only [bihimp,himp_eq,bitEq,sup_comm,inf_comm]

theorem imp_curry_r181 (a b c : B) : imp a (imp b c) = imp (a ⊓ b) c := by
  simp only [_root_.imp,compl_inf,sup_assoc]

@[simp] theorem mem_powerset_subset_r181 (x y : bSet B) :
    (x ∈ᴮ bSet.bv_powerset y) = (x ⊆ᴮ y) := by
  apply le_antisymm
  · exact bSet.bv_powerset_spec.mpr le_rfl
  · exact bSet.bv_powerset_spec.mp le_rfl

end SetLanguage
end JSP000933
