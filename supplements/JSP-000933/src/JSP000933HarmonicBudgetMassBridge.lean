import JSP000933ActualTruncatedHybrid

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem groundHarmBudget_real_mass_r339 (a b : Set ℕ) (k n : ℕ) :
    GroundBudgetHolds true a b k n ↔
      (k:ℝ)*(∑ m ∈ restrictSet (Finset.range n) (a \ b), harmonicEU.weight m)≤
        weightedPrefixSum harmonicEU.weight n := by
  classical
  let N := ∑ m ∈ restrictSet (Finset.range n) (a \ b), harmonicEU.weight m
  let D := weightedPrefixSum harmonicEU.weight n
  let U := groundScaledHarmonic false a b n n
  let V := groundScaledHarmonic true a b n n
  have hU : (U:ℝ)=(Nat.factorial n:ℝ)*N := by
    unfold U
    rw [scaledHarmonic_cast_helper_r203]
    congr 1
    unfold N restrictSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases he : m∈a \ b <;> simp [he,harmonicEU,harmonicAtom,Nat.cast_add]
  have hV : (V:ℝ)=(Nat.factorial n:ℝ)*D := by
    unfold V
    rw [scaledHarmonic_cast_helper_r203]
    simp [D,weightedPrefixSum,harmonicEU,harmonicAtom,Nat.cast_add]
  have hFactor : (0:ℝ)<(Nat.factorial n:ℝ) := by exact_mod_cast Nat.factorial_pos n
  change k*U≤V ↔ (k:ℝ)*N≤D
  constructor
  · intro h
    have hh : (k:ℝ)*(U:ℝ)≤(V:ℝ) := by exact_mod_cast h
    rw [hU,hV] at hh
    apply (mul_le_mul_iff_left₀ hFactor).mp
    calc
      ((k : ℝ) * N) * (Nat.factorial n : ℝ) = (k : ℝ) * ((Nat.factorial n : ℝ) * N) := by ring
      _ ≤ (Nat.factorial n : ℝ) * D := hh
      _ = D * (Nat.factorial n : ℝ) := mul_comm _ _
  · intro h
    have hh := mul_le_mul_of_nonneg_left h hFactor.le
    have he : (k:ℝ)*(U:ℝ)≤(V:ℝ) := by
      rw [hU,hV]
      simpa only [mul_assoc,mul_left_comm] using hh
    exact_mod_cast he

theorem groundHarmBudget_initialSegment_eventual_r339 (N k : ℕ) (hk : k≠0) :
    ∃ M : ℕ, ∀ n≥M, GroundBudgetHolds true (Set.Iio N) ∅ k n := by
  have hK : (0:ℝ)<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hN : WeightedNull harmonicEU.weight (Set.Iio N) := by
    have he : Set.Iio N=(Finset.range N : Set ℕ) := by ext x; simp
    rw [he]
    exact weightedNull_finset_of_eu harmonicEU _
  obtain ⟨M,hM⟩ := hN (1/(k:ℝ)) (one_div_pos.mpr hK)
  refine ⟨max M 1,fun n hn => ?_⟩
  have hPos : 0<n := (show 0<1 by decide).trans_le ((le_max_right M 1).trans hn)
  have hD : 0<weightedPrefixSum harmonicEU.weight n := by
    unfold weightedPrefixSum
    exact Finset.sum_pos (fun m _ => harmonicEU.pos m) ⟨0,Finset.mem_range.mpr hPos⟩
  have hE := hM n ((le_max_left M 1).trans hn)
  change (∑ m ∈ restrictSet (Finset.range n) (Set.Iio N), harmonicEU.weight m) /
    weightedPrefixSum harmonicEU.weight n ≤ 1/(k:ℝ) at hE
  have hV := mul_le_mul_of_nonneg_left ((div_le_iff₀ hD).mp hE) hK.le
  apply (groundHarmBudget_real_mass_r339 _ _ _ _).mpr
  rw [Set.sdiff_empty]
  refine hV.trans_eq ?_
  field_simp [ne_of_gt hK] <;> ring

end SetLanguage
end JSP000933
