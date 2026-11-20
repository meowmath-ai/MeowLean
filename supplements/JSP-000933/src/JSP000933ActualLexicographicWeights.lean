import JSP000933ActualFeasibilityRegularity

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualFiberFeasible_binary_r281 (K : Word × Word → B) (x : ℕ → B) (u : Word) :
    actualFiberFeasible K x u=actualFiberFeasible K x (u++[false])⊔actualFiberFeasible K x (u++[true]) := by
  rw [actualFiberFeasible_eq_finite_potential_r277 K x u,
    actualFiberFeasible_eq_finite_potential_r277 K x (u++[false]),
    actualFiberFeasible_eq_finite_potential_r277 K x (u++[true])]
  exact closedPotential_binary_r222 (namedRowOpen K x) u

def lexReverseWeight (f : Word → B) : Word → B
  | [] => f []
  | b::u => lexReverseWeight f u ⊓ (if b then (f (u.reverse++[false]))ᶜ else f (u.reverse++[false]))

def namedLexWordWeight (f : Word → B) (u : Word) : B :=
  lexReverseWeight f u.reverse

@[simp] theorem namedLexWordWeight_nil_r281 (f : Word → B) : namedLexWordWeight f []=f [] := rfl

theorem namedLexWordWeight_false_r281 (f : Word → B) (u : Word) :
    namedLexWordWeight f (u++[false])=namedLexWordWeight f u⊓f (u++[false]) := by
  simp [namedLexWordWeight,List.reverse_append,lexReverseWeight]

theorem namedLexWordWeight_true_r281 (f : Word → B) (u : Word) :
    namedLexWordWeight f (u++[true])=namedLexWordWeight f u⊓(f (u++[false]))ᶜ := by
  simp [namedLexWordWeight,List.reverse_append,lexReverseWeight]

theorem namedLexWordWeight_split_r281 (f : Word → B) (u : Word) :
    namedLexWordWeight f (u++[false])⊔namedLexWordWeight f (u++[true])=namedLexWordWeight f u := by
  rw [namedLexWordWeight_false_r281,namedLexWordWeight_true_r281,← inf_sup_left,sup_compl_eq_top,inf_top_eq]

theorem namedLexWordWeight_le_feasible_r281 (f : Word → B)
    (hf : ∀ u, f u=f (u++[false])⊔f (u++[true])) (u : Word) : namedLexWordWeight f u≤f u := by
  have h (v : Word) : lexReverseWeight f v≤f v.reverse := by
    induction v with
    | nil => exact le_rfl
    | cons b v ih =>
      cases b
      · rw [List.reverse_cons]
        change lexReverseWeight f v⊓f (v.reverse++[false])≤f (v.reverse++[false])
        exact inf_le_right
      · let a := f (v.reverse++[false])
        let d := f (v.reverse++[true])
        let r := lexReverseWeight f v⊓aᶜ
        have hr : r≤a⊔d := (inf_le_left.trans ih).trans_eq (hf v.reverse)
        have h0 : r⊓a≤⊥ :=
          (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot'
        have hd : r≤d := calc
          r = r⊓(a⊔d) := le_antisymm (le_inf le_rfl hr) inf_le_left
          _ = (r⊓a)⊔(r⊓d) := inf_sup_left _ _ _
          _ ≤ d := sup_le (h0.trans bot_le) inf_le_right
        rw [List.reverse_cons]
        change r≤f (v.reverse++[true])
        exact hd
  simpa only [namedLexWordWeight,List.reverse_reverse] using h u.reverse

theorem namedLexWordWeight_mask_r281 (p : B) {f g : Word → B} (N : ℕ)
    (h : ∀ u, u.length≤N → p⊓f u=p⊓g u) (u : Word) (hu : u.length≤N) :
    p⊓namedLexWordWeight f u=p⊓namedLexWordWeight g u := by
  have hR : ∀ v : Word, v.length≤N → p⊓lexReverseWeight f v=p⊓lexReverseWeight g v := by
    intro v
    induction v with
    | nil =>
      intro hN
      exact h [] hN
    | cons b v ih =>
      intro hN
      have h₁ : v.length≤N := by simp only [List.length_cons] at hN; omega
      have h₂ : (v.reverse++[false]).length≤N := by
        simpa only [List.length_append,List.length_reverse,List.length_cons,List.length_nil] using hN
      cases b
      · exact mask_inf_congr_r126 (ih h₁) (h _ h₂)
      · exact mask_inf_congr_r126 (ih h₁) (mask_compl_congr_r126 (h _ h₂))
  exact hR u.reverse (by simpa only [List.length_reverse] using hu)

end SetLanguage
end JSP000933
