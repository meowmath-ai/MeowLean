import JSP000933IntegerBudgetLimit
import ErdosProblems.Erdos1123.LogarithmicBlocks

open Filter Erdos1123
open scoped BigOperators Topology

namespace JSP000933
namespace SetLanguage

open PositiveForcing

theorem range_succ_map_eq_Ioc_r203 (n : ℕ) :
    (Finset.range n).map ⟨Nat.succ,Nat.succ_injective⟩ = Finset.Ioc 0 n := by
  ext j
  simp only [Finset.mem_map,Finset.mem_range,Finset.mem_Ioc,Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · intro hj
    cases j with
    | zero => omega
    | succ i => exact ⟨i,by omega,rfl⟩

open scoped Classical in
theorem cumulative_shift_r203 (w : ℕ → ℝ) (A : Set ℕ) (n : ℕ) :
    cumulative w A n =
      ∑ i ∈ Finset.range n, if i ∈ fromPositive A then w (i+1) else 0 := by
  classical
  unfold cumulative
  rw [← range_succ_map_eq_Ioc_r203 n,Finset.sum_map] <;> rfl

theorem fromPositive_diff_r203 (A C : Set ℕ) :
    fromPositive (A \ C) = fromPositive A \ fromPositive C := rfl

theorem groundCount_cast_cumulative_r203 (A C : Set ℕ) (n : ℕ) :
    (groundCount (fromPositive A) (fromPositive C) n : ℝ) = cumulative (fun _ => 1) (A \ C) n := by
  classical
  rw [cumulative_shift_r203,fromPositive_diff_r203]
  unfold groundCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i ∈ fromPositive A \ fromPositive C <;> simp [h]

open scoped Classical in
theorem scaledHarmonic_cast_helper_r203 (allBits : Bool) (A C : Set ℕ) (n : ℕ) :
    (groundScaledHarmonic allBits A C n n : ℝ) =
      (Nat.factorial n:ℝ) *
        ∑ i ∈ Finset.range n, if allBits=true ∨ i ∈ A \ C then ((i+1:ℕ):ℝ)⁻¹ else 0 := by
  classical
  unfold groundScaledHarmonic
  rw [Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt := Finset.mem_range.mp hi
  by_cases h : allBits=true ∨ i ∈ A \ C
  · rw [ite_eq_left h,ite_eq_left h,← div_eq_mul_inv]
    have hpos : 0 < i+1 := Nat.succ_pos i
    have hd : i+1 ∣ Nat.factorial n := Nat.dvd_factorial hpos (Nat.succ_le_of_lt hlt)
    apply (eq_div_iff (by exact_mod_cast (ne_of_gt hpos))).2
    exact_mod_cast Nat.div_mul_cancel hd
  · simp only [ite_eq_right h,Nat.cast_zero,mul_zero]

theorem scaledHarmonic_false_cast_r203 (A C : Set ℕ) (n : ℕ) :
    (groundScaledHarmonic false (fromPositive A) (fromPositive C) n n : ℝ) =
      (Nat.factorial n:ℝ) * cumulative (fun m => (m:ℝ)⁻¹) (A \ C) n := by
  classical
  rw [scaledHarmonic_cast_helper_r203,cumulative_shift_r203,fromPositive_diff_r203]
  simp

theorem scaledHarmonic_true_cast_r203 (A C : Set ℕ) (n : ℕ) :
    (groundScaledHarmonic true (fromPositive A) (fromPositive C) n n : ℝ) =
      (Nat.factorial n:ℝ) * cumulative (fun m => (m:ℝ)⁻¹) Set.univ n := by
  classical
  rw [scaledHarmonic_cast_helper_r203,cumulative_shift_r203]
  simp [fromPositive]

theorem ordinaryIntegerNull_blocks_iff_r203 (A C : Set ℕ) :
    OrdinaryIntegerNull (fromPositive A) (fromPositive C) ↔ ordinaryBlocks.IsNull (A \ C) := by
  unfold OrdinaryIntegerNull
  rw [integerBudget_iff_ratio_r202 _ _ ⟨1,fun n hn => hn⟩,ordinaryBlocks_null_iff]
  unfold WeightSequence.IsNull
  simp only [groundCount_cast_cumulative_r203]
  rw [funext (ordinary_mass_cumulative (A \ C))]

end SetLanguage
end JSP000933
