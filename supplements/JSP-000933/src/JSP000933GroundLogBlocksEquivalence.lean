import JSP000933PositiveShiftedMasses
import Mathlib.NumberTheory.Harmonic.Bounds

open Filter Erdos1123
open scoped Topology

namespace JSP000933
namespace SetLanguage

open PositiveForcing

theorem log_harmonic_eventual_bounds_r204 :
    ∃ N : ℕ, ∀ n ≥ N,
      0 < Real.log (n:ℝ) ∧ Real.log (n:ℝ) ≤ cumulative (fun m => (m:ℝ)⁻¹) Set.univ n ∧
        cumulative (fun m => (m:ℝ)⁻¹) Set.univ n ≤ 2*Real.log (n:ℝ) := by
  obtain ⟨N,hN⟩ := tendsto_atTop_atTop.mp nat_log_tendsto_atTop 1
  refine ⟨N,fun n hn => ?_⟩
  have h1 : (1:ℝ) ≤ Real.log (n:ℝ) := hN n hn
  refine ⟨zero_lt_one.trans_le h1,?_,?_⟩
  · rw [cumulative_inv_univ]
    exact log_le_harmonic n
  · rw [cumulative_inv_univ]
    exact (harmonic_le_one_add_log n).trans (by linarith)

theorem logarithmic_harmonic_ratio_iff_r204 (D : Set ℕ) :
    Tendsto (fun n => cumulative (fun m => (m:ℝ)⁻¹) D n /
      cumulative (fun m => (m:ℝ)⁻¹) Set.univ n) atTop (𝓝 0) ↔ logarithmicWeights.IsNull D := by
  let S (n : ℕ) := cumulative (fun m => (m:ℝ)⁻¹) D n
  let H (n : ℕ) := cumulative (fun m => (m:ℝ)⁻¹) Set.univ n
  let L (n : ℕ) := Real.log (n:ℝ)
  unfold WeightSequence.IsNull
  rw [funext (logarithmic_mass_cumulative D)]
  change Tendsto (fun n => S n / H n) atTop (𝓝 0) ↔ Tendsto (fun n => S n / L n) atTop (𝓝 0)
  obtain ⟨N,hN⟩ := log_harmonic_eventual_bounds_r204
  have hp (n : ℕ) : 0 ≤ S n := cumulative_nonneg (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) _ _
  constructor
  · intro h
    apply nonneg_tendsto_zero_of_eventual_bound_r202 _ _ 2 (by norm_num) h
    refine ⟨N,fun n hn => ?_⟩
    have ⟨hL,hLH,hHL⟩ := hN n hn
    have hH := hL.trans_le hLH
    refine ⟨div_nonneg (hp n) hL.le,div_nonneg (hp n) hH.le,?_⟩
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hL hH).2
    calc
      S n * H n ≤ S n * (2*L n) := mul_le_mul_of_nonneg_left hHL (hp n)
      _ = 2 * S n * L n := by ring
  · intro h
    apply nonneg_tendsto_zero_of_eventual_bound_r202 _ _ 1 (by norm_num) h
    refine ⟨N,fun n hn => ?_⟩
    have ⟨hL,hLH,_⟩ := hN n hn
    have hH := hL.trans_le hLH
    refine ⟨div_nonneg (hp n) hH.le,div_nonneg (hp n) hL.le,?_⟩
    rw [one_mul]
    exact div_le_div_of_nonneg_left (hp n) hL hLH

theorem harmonicIntegerNull_blocks_iff_r204 (A C : Set ℕ) :
    HarmonicIntegerNull (fromPositive A) (fromPositive C) ↔ logarithmicBlocks.IsNull (A \ C) := by
  let u (n : ℕ) := groundScaledHarmonic false (fromPositive A) (fromPositive C) n n
  let v (n : ℕ) := groundScaledHarmonic true (fromPositive A) (fromPositive C) n n
  have hf (n : ℕ) : (0:ℝ) < (Nat.factorial n:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hv : ∃ N : ℕ, ∀ n ≥ N, 0 < v n := by
    obtain ⟨N,hN⟩ := log_harmonic_eventual_bounds_r204
    refine ⟨N,fun n hn => ?_⟩
    have hH := (hN n hn).1.trans_le (hN n hn).2.1
    have hR : (0:ℝ) < (v n:ℝ) := by
      change (0:ℝ) < (groundScaledHarmonic true (fromPositive A) (fromPositive C) n n:ℝ)
      rw [scaledHarmonic_true_cast_r203]
      exact mul_pos (hf n) hH
    exact_mod_cast hR
  have hfun :
      (fun n => (u n:ℝ)/(v n:ℝ)) = (fun n => cumulative (fun m => (m:ℝ)⁻¹) (A \ C) n /
        cumulative (fun m => (m:ℝ)⁻¹) Set.univ n) := by
    funext n
    dsimp only [u,v]
    rw [scaledHarmonic_false_cast_r203,scaledHarmonic_true_cast_r203]
    exact mul_div_mul_left _ _ (ne_of_gt (hf n))
  change EventuallyIntegerBudget (fun k n => k*u n ≤ v n) ↔ _
  rw [integerBudget_iff_ratio_r202 u v hv,hfun,logarithmicBlocks_null_iff]
  exact logarithmic_harmonic_ratio_iff_r204 (A \ C)

end SetLanguage
end JSP000933
