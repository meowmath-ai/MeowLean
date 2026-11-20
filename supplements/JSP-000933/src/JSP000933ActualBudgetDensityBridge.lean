import JSP000933ActualNoncollapse
import JSP000933CSPD
import JSP000933ArithmeticGraph

open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

theorem groundOrdBudget_iff_density_r386 (A : Set ℕ) {k n : ℕ} (hk : 0<k) (hn : 0<n) :
    GroundBudgetHolds false A ∅ k n ↔
      weightedSetDensity ordinaryEU.weight A n≤(k : ℝ)⁻¹ := by
  classical
  rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
  have hD : groundBudgetDenom false n=n := by simp [groundBudgetDenom,groundBudgetWeight]
  rw [hD]
  have he : groundBudgetMass false n A=ordinaryIntegerMass A n := by
    unfold groundBudgetMass ordinaryIntegerMass restrictSet
    change (∑ m ∈ Finset.range n, if m∈A then 1 else 0)=((Finset.range n).filter (fun m => m∈A)).card
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact ordinaryArithmeticBudget_iff A hk hn

theorem groundHarBudget_iff_logDensity_r386 (D : Finset ℕ) {k n : ℕ} (hk : 0<k) :
    GroundBudgetHolds true (D : Set ℕ) ∅ k n ↔ logPrefixDensity D n≤(k : ℝ)⁻¹ := by
  classical
  by_cases hn : n=0
  · subst n
    simp [GroundBudgetHolds,groundScaledHarmonic,logPrefixDensity,logPrefixMass,harmonicSum,prefixBlock]
  rw [groundHarmBudget_real_mass_r339,Set.sdiff_empty,logPrefixDensity_eq_weightedSetDensity]
  let S := ∑ m ∈ restrictSet (Finset.range n) (D : Set ℕ),harmonicEU.weight m
  let M := weightedPrefixSum harmonicEU.weight n
  have hM : 0<M := by
    unfold M weightedPrefixSum
    exact Finset.sum_pos (fun i _ => harmonicEU.pos i) ⟨0,Finset.mem_range.mpr (Nat.pos_of_ne_zero hn)⟩
  have hK : 0<(k : ℝ) := by exact_mod_cast hk
  change (k : ℝ)*S≤M ↔ S/M≤(k : ℝ)⁻¹
  rw [div_le_iff₀ hM,show (k : ℝ)⁻¹*M=M/(k : ℝ) by rw [div_eq_mul_inv,mul_comm],
    le_div_iff₀ hK,mul_comm S (k : ℝ)]

theorem groundAllHarBudgets_iff_concentration_r386 (D : Finset ℕ) (k : ℕ) (hk : 0<k) :
    GroundAllBudgets true k D ↔ logConcentration D≤(k : ℝ)⁻¹ := by
  rw [logConcentration_le_iff]
  exact ⟨fun h n => (groundHarBudget_iff_logDensity_r386 D hk).mp (h n),
    fun h n => (groundHarBudget_iff_logDensity_r386 D hk).mpr (h n)⟩

theorem not_allOrdBudgets_of_prefix_r386 (D : Finset ℕ)
    (h : PrefixExceeds ordinaryEU D (1/4)) : ¬GroundAllBudgets false 4 D := by
  obtain ⟨n,hn⟩ := h
  have hP : 0<n := by
    by_contra h0
    have he : n=0 := by omega
    subst n
    have hZero : weightedSetDensity ordinaryEU.weight (D : Set ℕ) 0=0 := by
      simp [weightedSetDensity,weightedPrefixSum]
    rw [hZero] at hn
    norm_num at hn
  intro hD
  have hSmall := (groundOrdBudget_iff_density_r386 (D : Set ℕ) (by decide : 0<4) hP).mp (hD n)
  have hSmall' : weightedSetDensity ordinaryEU.weight (D : Set ℕ) n≤1/4 := by
    simpa only [one_div, Nat.cast_ofNat] using hSmall
  exact not_lt_of_ge hSmall' hn

theorem card_justSourceBlock_r386 (i : ℕ) :
    (justSourceBlock i).card≤justSourceStart i*2^justSourceStart i := by
  change (Finset.Ico (justSourceStart i) (justSourceStart i*2^justSourceStart i)).card≤_
  rw [Nat.card_Ico]
  omega

theorem linear_escape_cutoff_r386 {K n m : ℕ} {α : ℝ}
    (hK : 16/α≤(K : ℝ)) (hm : K*(n+1)≤ m) :
    16*((n : ℝ)+1)/α≤(m : ℝ)+1 := by
  have hM : (K : ℝ)*((n : ℝ)+1)≤(m : ℝ) := by exact_mod_cast hm
  calc
    _=(16/α)*((n : ℝ)+1) := by ring
    _≤(K : ℝ)*((n : ℝ)+1) := mul_le_mul_of_nonneg_right hK (by positivity)
    _≤(m : ℝ) := hM
    _≤(m : ℝ)+1 := le_add_of_nonneg_right zero_le_one

end SetLanguage
end JSP000933
