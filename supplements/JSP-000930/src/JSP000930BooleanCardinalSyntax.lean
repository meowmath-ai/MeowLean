import JSP000930WetzelSentence
import JSP000933BooleanSentenceLanguage

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930
namespace SetLanguage

open JSP000933.SetLanguage

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem trunc_zero {α : Type*} {n : ℕ} (v : DVec α n) :
    DVec.trunc 0 (Nat.zero_le n) v = DVec.nil := by
  cases v
  · rfl
  · rfl

private theorem bTruth_and_r6 {n : ℕ} (v : DVec (V B) n) (φ ψ : SForm n) :
    bTruth v (bd_and φ ψ) = bTruth v φ ⊓ bTruth v ψ :=
  boolean_realize_bounded_formula_and

private theorem bTruth_not_r6 {n : ℕ} (v : DVec (V B) n) (φ : SForm n) :
    bTruth v (bd_not φ) = (bTruth v φ)ᶜ :=
  boolean_realize_bounded_formula_not

private theorem eq_guard_exists (X : bSet B) (P : bSet B → B)
    (hP : bSet.B_ext P) :
    (⨆ x : bSet B, (X =ᴮ x) ⊓ P x) = P X := by
  apply le_antisymm
  · apply iSup_le
    intro x
    exact (le_inf (inf_le_left.trans_eq bSet.bv_eq_symm) inf_le_right).trans (hP x X)
  · apply le_iSup_of_le X
    have hx : (X =ᴮ X) = (⊤ : B) := top_unique bSet.bv_refl
    rw [hx, top_inf_eq]

theorem bTruth_ordinal_f_r6 {n : ℕ} (v : DVec (V B) n) (a : STerm n) :
    bTruth v (ordinal_f a) = bSet.Ord (bTerm v a) := by
  simp only [ordinal_f, bTruth_sEx_r181, bTruth_and_r6]
  refine Eq.trans (iSup_congr (fun x : bSet B => ?_))
    (eq_guard_exists (bTerm v a) bSet.Ord bSet.B_ext_Ord)
  congr 1
  · exact (bTruth_equal_r181 _ _ _).trans
      (congrArg₂ (fun (u w : bSet B) => (u =ᴮ w))
        (bTerm_up_r181 v x a) (bTerm_current_r181 v x))
  · simp only [bTruth, boolean_realize_cast_bounded_formula, DVec.trunc, trunc_zero, Ord_f_is_Ord]

theorem bTruth_injects_f_r6 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (injects_f a b) = bSet.injects_into (bTerm v a) (bTerm v b) := by
  simp only [injects_f, bTruth_sEx_r181, bTruth_and_r6]
  let X := bTerm v a
  let Y := bTerm v b
  let U (x y : bSet B) : B := (X =ᴮ x) ⊓ ((Y =ᴮ y) ⊓ bSet.injects_into x y)
  refine Eq.trans (b := ⨆ x : bSet B, ⨆ y : bSet B, U x y) ?_ ?_
  · apply iSup_congr
    intro x
    apply iSup_congr
    intro y
    have hx : bTerm (DVec.cons y (DVec.cons x v))
        (up (bd_var ⟨0, Nat.succ_pos n⟩)) = x :=
      (bTerm_up_r181 (DVec.cons x v) y _).trans (bTerm_current_r181 v x)
    have hy := bTerm_current_r181 (DVec.cons x v) y
    have he : bTruth (DVec.cons y (DVec.cons x v)) (injects_into_f.cast (by omega)) =
        bSet.injects_into x y :=
      by simp only [bTruth, boolean_realize_cast_bounded_formula, DVec.trunc, trunc_zero, realize_injects_into]
    simp only [bTruth_equal_r181, bTerm_up2_r181 v x y a, bTerm_up2_r181 v x y b,
      hx, hy, he, X, Y, U]
  · calc
      _ = ⨆ x : bSet B, (X =ᴮ x) ⊓ bSet.injects_into x Y := by
        apply iSup_congr
        intro x
        change (⨆ y : bSet B, (X =ᴮ x) ⊓ ((Y =ᴮ y) ⊓ bSet.injects_into x y)) = _
        rw [← inf_iSup_eq]
        rw [eq_guard_exists Y (fun y => bSet.injects_into x y) bSet.B_ext_injects_into_right]
      _ = _ := eq_guard_exists X (fun x => bSet.injects_into x Y) bSet.B_ext_injects_into_left

theorem bTruth_sameCard_f_r6 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (sameCard_f a b) =
      bSet.injects_into (bTerm v a) (bTerm v b) ⊓
        bSet.injects_into (bTerm v b) (bTerm v a) := by
  simp only [sameCard_f, boolean_realize_bounded_formula_and, bTruth_injects_f_r6]

theorem bTruth_strictCard_f_r6 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (strictCard_f a b) =
      bSet.injects_into (bTerm v a) (bTerm v b) ⊓
        (bSet.injects_into (bTerm v b) (bTerm v a))ᶜ := by
  simp only [strictCard_f, boolean_realize_bounded_formula_and,
    bTruth_not_r6, bTruth_injects_f_r6]

noncomputable def nextInitialCard (a b : bSet B) : B :=
  bSet.Ord b ⊓
    ((bSet.injects_into a b ⊓ (bSet.injects_into b a)ᶜ) ⊓
      (⨅ c : bSet B, imp (c ∈ᴮ b) (bSet.injects_into c a)))

theorem bTruth_nextInitialCard_f_r6 {n : ℕ} (v : DVec (V B) n) (a b : STerm n) :
    bTruth v (nextInitialCard_f a b) = nextInitialCard (bTerm v a) (bTerm v b) := by
  have h (x : bSet B) :
      bTruth (DVec.cons x v) (injects_f (bd_var ⟨0, Nat.succ_pos n⟩) (up a)) =
        bSet.injects_into x (bTerm v a) :=
    (bTruth_injects_f_r6 _ _ _).trans
      (congrArg₂ bSet.injects_into (bTerm_current_r181 v x) (bTerm_up_r181 v x a))
  simp only [nextInitialCard_f, nextInitialCard, bTruth_and_r6,
    bTruth_ordinal_f_r6, bTruth_strictCard_f_r6, bTruth_allIn_r181, h]

private theorem bTerm_omega_r6 {n : ℕ} (v : DVec (V B) n) :
    bTerm v omega = bSet.omega :=
  boolean_realize_bounded_term_omega'

private theorem bTerm_omegaSubsets_r6 {n : ℕ} (v : DVec (V B) n) :
    bTerm v omegaSubsets = bSet.bv_powerset bSet.omega := by
  simp only [omegaSubsets, powerset, omega, boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_omega']

theorem bTruth_continuumAlephTwo_f_r6 :
    bTruth (B := B) DVec.nil continuumAlephTwo_f =
      ⨆ a₁ : bSet B, ⨆ a₂ : bSet B,
        nextInitialCard bSet.omega a₁ ⊓
          (nextInitialCard a₁ a₂ ⊓
            (bSet.injects_into a₂ (bSet.bv_powerset bSet.omega) ⊓
              bSet.injects_into (bSet.bv_powerset bSet.omega) a₂)) := by
  simp only [continuumAlephTwo_f, bTruth_sEx_r181, bTruth_and_r6]
  apply iSup_congr
  intro a₁
  apply iSup_congr
  intro a₂
  let v : DVec (V B) 2 := DVec.cons a₂ (DVec.cons a₁ DVec.nil)
  let a : STerm 1 := bd_var ⟨0, by decide⟩
  let b : STerm 2 := bd_var ⟨0, by decide⟩
  have ha : bTerm v (up a) = a₁ :=
    (bTerm_up_r181 (DVec.cons a₁ DVec.nil) a₂ a).trans (bTerm_current_r181 DVec.nil a₁)
  have hb : bTerm v b = a₂ := bTerm_current_r181 (DVec.cons a₁ DVec.nil) a₂
  change bTruth v (nextInitialCard_f omega (up a)) ⊓
    (bTruth v (nextInitialCard_f (up a) b) ⊓ bTruth v (sameCard_f b omegaSubsets)) = _
  rw [bTruth_nextInitialCard_f_r6, bTruth_nextInitialCard_f_r6, bTruth_sameCard_f_r6,
    bTerm_omega_r6, bTerm_omegaSubsets_r6, ha, hb]

theorem forces_continuumAlephTwo_f_r6 {Γ : B} {a₁ a₂ : bSet B}
    (h₁ : Γ ≤ nextInitialCard bSet.omega a₁)
    (h₂ : Γ ≤ nextInitialCard a₁ a₂)
    (hc : Γ ≤ bSet.injects_into a₂ (bSet.bv_powerset bSet.omega))
    (hc' : Γ ≤ bSet.injects_into (bSet.bv_powerset bSet.omega) a₂) :
    Γ ⊩[V B] continuumAlephTwo_f := by
  change Γ ≤ bTruth DVec.nil continuumAlephTwo_f
  rw [bTruth_continuumAlephTwo_f_r6]
  exact le_iSup_of_le a₁ (le_iSup_of_le a₂ (le_inf h₁ (le_inf h₂ (le_inf hc hc'))))

end SetLanguage
end JSP000930
