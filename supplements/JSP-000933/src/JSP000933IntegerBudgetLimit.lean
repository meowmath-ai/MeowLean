import JSP000933EventualBudgetValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Filter
open scoped Topology

namespace JSP000933
namespace SetLanguage

theorem integerBudget_iff_ratio_r202 (num den : ℕ → ℕ)
    (hDen : ∃ N : ℕ, ∀ n ≥ N, 0 < den n) :
    EventuallyIntegerBudget (fun k n => k*num n ≤ den n) ↔
      Tendsto (fun n => (num n : ℝ)/(den n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := hDen
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
    have hkR : (0:ℝ) < (k:ℝ) := (div_pos zero_lt_one hε).trans hk
    have hk0 : k ≠ 0 := ne_of_gt (by exact_mod_cast hkR)
    have hSmall : (1:ℝ)/(k:ℝ) < ε := by
      apply (div_lt_iff₀ hkR).2
      have he := (div_lt_iff₀ hε).mp hk
      simpa only [mul_comm] using he
    obtain ⟨M,hM⟩ := h k hk0
    refine ⟨max M N,fun n hn => ?_⟩
    have hd : (0:ℝ) < (den n:ℝ) := by exact_mod_cast hN n ((le_max_right M N).trans hn)
    have hBudget : k*num n ≤ den n := hM n ((le_max_left M N).trans hn)
    have hR : (num n:ℝ)/(den n:ℝ) ≤ 1/(k:ℝ) := by
      apply (div_le_div_iff₀ hd hkR).2
      rw [one_mul,mul_comm]
      exact_mod_cast hBudget
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hd.le)]
    exact hR.trans_lt hSmall
  · intro h k hk
    have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    obtain ⟨M,hM⟩ := h ((1:ℝ)/(k:ℝ)) (div_pos zero_lt_one hkR)
    refine ⟨max M N,fun n hn => ?_⟩
    have hd : (0:ℝ) < (den n:ℝ) := by exact_mod_cast hN n ((le_max_right M N).trans hn)
    have hR := hM n ((le_max_left M N).trans hn)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hd.le)] at hR
    have he := (div_lt_div_iff₀ hd hkR).mp hR
    rw [one_mul,mul_comm] at he
    exact_mod_cast he.le

theorem nonneg_tendsto_zero_of_eventual_bound_r202 (a b : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ a n ∧ 0 ≤ b n ∧ a n ≤ C*b n) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := h
  rw [Metric.tendsto_atTop] at hb ⊢
  intro ε hε
  obtain ⟨M,hM⟩ := hb (ε/C) (div_pos hε hC)
  refine ⟨max M N,fun n hn => ?_⟩
  have h0 := hN n ((le_max_right M N).trans hn)
  have he := hM n ((le_max_left M N).trans hn)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg h0.2.1] at he
  rw [Real.dist_eq,sub_zero,abs_of_nonneg h0.1]
  exact h0.2.2.trans_lt (by
    rw [mul_comm]
    exact (lt_div_iff₀ hC).mp he)

end SetLanguage
end JSP000933
