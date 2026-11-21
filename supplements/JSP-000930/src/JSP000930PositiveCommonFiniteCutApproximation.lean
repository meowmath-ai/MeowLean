import JSP000930PositiveMixedRationalGroundCompletion

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] [Countable J] [Nonempty J]

theorem dist_lt_of_common_rational_box {n : ℕ} (b : narrowRationalPair n)
    {x y : ℝ}
    (hx₁ : (b.val.1.value : ℝ) ≤ x) (hx₂ : x ≤ (b.val.2.value : ℝ))
    (hy₁ : (b.val.1.value : ℝ) ≤ y) (hy₂ : y ≤ (b.val.2.value : ℝ)) :
    dist x y < (1/2 : ℝ)^n := by
  have hwidth : (b.val.2.value : ℝ) - (b.val.1.value : ℝ) < (1/2 : ℝ)^n := by
    let scale : ℚ := (1/2 : ℚ)^n
    have h : ((b.val.2.value - b.val.1.value : ℚ) : ℝ) < (scale : ℝ) :=
      Rat.cast_lt.mpr b.property.2
    dsimp only [scale] at h
    push_cast at h
    exact h
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem positive_common_finite_cut_approximation
    {X : ℕ → Type} (β : J → RatPresentation → B)
    (V : ∀ n,X n → B) (p : ℕ → B) (select : ∀ n,X n)
    (z : J → ℝ) (box : ∀ j : J,∀ n : ℕ,narrowRationalPair n)
    (hAnti : Antitone p) (hNZ : ∀ n,p n ≠ ⊥)
    (hV : ∀ n,p n ≤ V n (select n))
    (hbox : ∀ j n,
      RationalEncloses (β j) (box j n).val.1 (box j n).val.2 (p (cutCoordIndex j n)) ∧
        ((box j n).val.1.value : ℝ) ≤ z j ∧ z j ≤ ((box j n).val.2.value : ℝ))
    (requiredCuts : Finset (J × ℕ)) (requiredTests : Finset ℕ) :
    ∃ k, p k ≠ ⊥ ∧
      (∀ n ∈ requiredTests,p k ≤ V n (select n)) ∧
      ∀ j n, (j,n) ∈ requiredCuts →
        RationalEncloses (β j) (box j n).val.1 (box j n).val.2 (p k) ∧
        ∀ y : ℝ, ((box j n).val.1.value : ℝ) ≤ y →
          y ≤ ((box j n).val.2.value : ℝ) → dist y (z j) < (1/2 : ℝ)^n := by
  classical
  let k := max (requiredCuts.sup (fun a => cutCoordIndex a.1 a.2)) (requiredTests.sup id)
  refine ⟨k,hNZ k,?_,?_⟩
  · intro n hn
    have h₁ : n ≤ requiredTests.sup id :=
      Finset.le_sup (f := id) hn
    exact (hAnti (h₁.trans (le_max_right _ _))).trans (hV n)
  · intro j n hn
    have h₁ : cutCoordIndex j n ≤ requiredCuts.sup (fun a => cutCoordIndex a.1 a.2) :=
      Finset.le_sup (f := fun a : J × ℕ => cutCoordIndex a.1 a.2) hn
    have hkp : p k ≤ p (cutCoordIndex j n) := hAnti (h₁.trans (le_max_left _ _))
    rcases hbox j n with ⟨⟨hlo,hhi⟩,hz₁,hz₂⟩
    exact ⟨⟨hkp.trans hlo,hkp.trans hhi⟩,fun y hy₁ hy₂ =>
      dist_lt_of_common_rational_box (box j n) hy₁ hy₂ hz₁ hz₂⟩

end JSP000930.Positive
