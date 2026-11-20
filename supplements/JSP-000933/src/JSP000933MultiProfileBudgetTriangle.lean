import JSP000933BudgetFiniteLocality
import JSP000933BooleanOpenCodeDensity

open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_joint_finiteGroundProfiles_r227 {I : Type} [Fintype I]
    (a : I → bSet B) (n : ℕ) (p : B) (hp : p ≠ ⊥) :
    ∃ r : I → Set ℕ, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧
      ∀ j i, i<n →
        q ⊓ membershipBits (a j) i = q ⊓ membershipBits (groundSubsetName B (r j)) i := by
  let W := {u : Word // u.length=n}
  let T (j : I) (u : W) := cylinderValue (membershipBits (a j)) u.1
  have h (j : I) : p ≤ ⨆ u : W, T j u := by
    apply le_of_dense_named_refinements_r219
    intro q hq hqp
    obtain ⟨u,hu,r,hr,hrq,hru⟩ := exists_decided_initialWord_r136 (membershipBits (a j)) n q hq
    exact ⟨r,hr,hrq,le_iSup_of_le ⟨u,hu⟩ hru⟩
  obtain ⟨u,q,hq,hqp,hU⟩ := exists_nonzero_finiteChoices_r135 T p hp (le_iInf h)
  refine ⟨fun j => subsetFromWord (u j).1,q,hq,hqp,?_⟩
  intro j i hi
  exact cylinder_fixes_ground_membership_r211 (a j) (u j).1 (hU j) i ((u j).2.symm ▸ hi)

open scoped Classical in
theorem difference_weighted_triangle_r227 (w : ℕ → ℕ) (A M C : Set ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if i ∈ A \ C then w i else 0) ≤
      (∑ i ∈ Finset.range n, if i ∈ A \ M then w i else 0) +
        (∑ i ∈ Finset.range n, if i ∈ M \ C then w i else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i ∈ A <;> by_cases hm : i ∈ M <;> by_cases hc : i ∈ C <;>
    simp [ha,hm,hc] <;> omega

theorem groundCount_triangle_r227 (A M C : Set ℕ) (n : ℕ) :
    groundCount A C n ≤ groundCount A M n + groundCount M C n :=
  difference_weighted_triangle_r227 (fun _ => 1) A M C n

theorem groundScaledHarmonic_triangle_r227 (A M C : Set ℕ) (n : ℕ) :
    groundScaledHarmonic false A C n n ≤
      groundScaledHarmonic false A M n n + groundScaledHarmonic false M C n n := by
  classical
  simpa [groundScaledHarmonic] using
    difference_weighted_triangle_r227 (fun i => Nat.factorial n/(i+1)) A M C n

theorem groundScaledHarmonic_all_independent_r227 (A C A' C' : Set ℕ) (p n : ℕ) :
    groundScaledHarmonic true A C p n = groundScaledHarmonic true A' C' p n := by
  classical
  simp [groundScaledHarmonic]

end SetLanguage
end JSP000933
