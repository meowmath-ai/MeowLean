import JSP000933BooleanBudgetLiftingRule

open scoped BigOperators

namespace JSP000933
namespace SetLanguage

def groundBudgetWeight (h : Bool) (n i : ℕ) : ℕ :=
  if h then Nat.factorial n/(i+1) else 1

noncomputable def groundBudgetMass (h : Bool) (n : ℕ) (D : Set ℕ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if i∈D then groundBudgetWeight h n i else 0

def groundBudgetDenom (h : Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, groundBudgetWeight h n i

theorem groundBudgetHolds_weighted_r232 (h : Bool) (A C : Set ℕ) (k n : ℕ) :
    GroundBudgetHolds h A C k n ↔
      k*groundBudgetMass h n (A \ C) ≤ groundBudgetDenom h n := by
  classical
  cases h <;>
    simp [GroundBudgetHolds,groundBudgetMass,groundBudgetDenom,groundBudgetWeight,
      groundCount,groundScaledHarmonic]

theorem groundBudgetMass_mono_r232 (h : Bool) (n : ℕ) {A C : Set ℕ} (hAC : A ⊆ C) :
    groundBudgetMass h n A ≤ groundBudgetMass h n C := by
  classical
  unfold groundBudgetMass
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i∈A
  · simp [hi,hAC hi]
  · simp [hi]

theorem groundBudgetMass_union_r232 (h : Bool) (n : ℕ) (A C : Set ℕ) :
    groundBudgetMass h n (A ∪ C) ≤ groundBudgetMass h n A + groundBudgetMass h n C := by
  classical
  unfold groundBudgetMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i∈A <;> by_cases hj : i∈C <;> simp [hi,hj] <;> omega

theorem GroundBudgetHolds.of_diff_subset_r232 (h : Bool) (k n : ℕ)
    {A C D E : Set ℕ} (hAC : A \ C ⊆ D \ E) (hDE : GroundBudgetHolds h D E k n) :
    GroundBudgetHolds h A C k n := by
  rw [groundBudgetHolds_weighted_r232] at hDE ⊢
  exact (Nat.mul_le_mul_left k (groundBudgetMass_mono_r232 h n hAC)).trans hDE

theorem GroundBudgetHolds.of_diff_cover_r232 (h : Bool) (k n : ℕ)
    {A C D E F G : Set ℕ} (hCover : A \ C ⊆ (D \ E) ∪ (F \ G))
    (h1 : GroundBudgetHolds h D E (2*k) n) (h2 : GroundBudgetHolds h F G (2*k) n) :
    GroundBudgetHolds h A C k n := by
  rw [groundBudgetHolds_weighted_r232] at h1 h2 ⊢
  have hM := (groundBudgetMass_mono_r232 h n hCover).trans
    (groundBudgetMass_union_r232 h n (D \ E) (F \ G))
  apply (Nat.mul_le_mul_left k hM).trans
  rw [Nat.mul_assoc] at h1 h2
  rw [Nat.mul_add]
  omega

theorem GroundBudgetHolds.compl_iff_r232 (h : Bool) (k n : ℕ) (A C : Set ℕ) :
    GroundBudgetHolds h Cᶜ Aᶜ k n ↔ GroundBudgetHolds h A C k n := by
  classical
  have he : Cᶜ \ Aᶜ = A \ C := by
    ext i
    simp only [Set.mem_sdiff,Set.mem_compl_iff,not_not,and_comm]
  rw [groundBudgetHolds_weighted_r232,groundBudgetHolds_weighted_r232,he]

end SetLanguage
end JSP000933
