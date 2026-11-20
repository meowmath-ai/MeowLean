import JSP000933ActualTruncatedGroundPalette

open scoped Flypitch BigOperators

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem dyadic_natBudget_sum_r343 (D : ℕ) :
    ∀ L a : ℕ, ∀ M : ℕ → ℕ, (∀ i<L, ((2:ℕ)^i*(2*a))*M i≤D) →
      a*(∑ i ∈ Finset.range L,M i)≤D := by
  intro L
  induction L with
  | zero => intro a M h; simp
  | succ L ih =>
    intro a M h
    have hH : (2*a)*M 0≤D := by simpa using h 0 (Nat.zero_lt_succ L)
    have hT := ih (2*a) (fun i => M (i+1)) (fun i hi => by
      have hh := h (i+1) (Nat.succ_lt_succ hi)
      rw [pow_succ,(by ring : (2:ℕ)^i * 2 * (2*a) = (2:ℕ)^i * (2*(2*a)))] at hh
      exact hh)
    rw [Finset.sum_range_succ',Nat.mul_add]
    rw [Nat.mul_assoc] at hH hT
    omega

theorem groundBudgetMass_finite_union_r343 (h : Bool) (n : ℕ) (D : ℕ → Set ℕ) (L : ℕ) :
    groundBudgetMass h n {m | ∃ i<L, m∈D i} ≤ ∑ i ∈ Finset.range L,groundBudgetMass h n (D i) := by
  induction L with
  | zero => simp [groundBudgetMass]
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have he : {m | ∃ i<L+1, m∈D i}={m | ∃ i<L, m∈D i} ∪ D L := by
      ext m
      change (∃ i<L+1, m∈D i) ↔ (∃ i<L, m∈D i) ∨ m∈D L
      constructor
      · rintro ⟨i,hi,hm⟩
        by_cases he : i=L
        · exact Or.inr (he ▸ hm)
        · exact Or.inl ⟨i,by omega,hm⟩
      · rintro (⟨i,hi,hm⟩ | hm)
        · exact ⟨i,by omega,hm⟩
        · exact ⟨L,Nat.lt_succ_self L,hm⟩
    rw [he]
    exact (groundBudgetMass_union_r232 h n _ _).trans (Nat.add_le_add_right ih _)

theorem ground_xor_successive_witness_r343 (S : ℕ → Set ℕ) (J m : ℕ) :
    ∀ L, m∈xorSet (S J) (S (J+L)) →
      ∃ i<L, m∈xorSet (S (J+i)) (S (J+i+1)) := by
  intro L
  induction L with
  | zero => simp [xorSet]
  | succ L ih =>
    intro h
    by_cases he : m∈xorSet (S J) (S (J+L))
    · obtain ⟨i,hi,hM⟩ := ih he
      exact ⟨i,hi.trans (Nat.lt_succ_self L),hM⟩
    · refine ⟨L,Nat.lt_succ_self L,?_⟩
      simp only [xorSet,Set.mem_union,Set.mem_sdiff] at he h ⊢
      tauto

def groundCutDifference (S : ℕ → Set ℕ) (g : ℕ → ℕ) (j : ℕ) : Set ℕ :=
  xorSet (S j) (S (j+1)) ∩ Set.Ici (actualGroundHybridCut g (j+1))

theorem groundTruncated_errors_covered_r343 (S : ℕ → Set ℕ) (g : ℕ → ℕ) (J n : ℕ) :
    ∀ m<n, m∈xorSet (groundTruncatedHybrid S g J) (S J) →
      m∈({m | ∃ i<n, m∈groundCutDifference S g (J+i)} : Set ℕ) := by
  intro m hm hE
  let c := actualGroundHybridCut g
  let b := hybridBand c (actualGroundHybridCut_strict_r336 g) m
  have hBand := (hybridBand_spec c (actualGroundHybridCut_strict_r336 g)
    (actualGroundHybridCut_zero_r336 g) m).1
  have hB : b≤ m := (actualGroundHybridCut_le_self_of_index_r336 g b).trans hBand
  have hE' : m∈xorSet (S (max J b)) (S J) := hE
  by_cases hJ : J≤b
  · have hb : J+(b-J)=b := Nat.add_sub_of_le hJ
    rw [max_eq_right hJ] at hE'
    have hX : m∈xorSet (S J) (S (J+(b-J))) := by
      rw [hb]
      simp only [xorSet,Set.mem_union,Set.mem_sdiff] at hE' ⊢
      exact hE'.symm
    obtain ⟨i,hi,hI⟩ := ground_xor_successive_witness_r343 S J m (b-J) hX
    have hiB : J+i+1≤b := by omega
    refine ⟨i,by omega,hI,?_⟩
    exact ((actualGroundHybridCut_strict_r336 g).monotone hiB).trans hBand
  · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hJ))] at hE'
    exact False.elim (by simpa [xorSet] using hE')

theorem groundTruncated_dyadicBudget_r343 (S : ℕ → Set ℕ) (g : ℕ → ℕ) (J n : ℕ)
    (hG : ∀ j, actualGroundHybridCut g (j+1)≤n →
      GroundBudgetHolds true (xorSet (S j) (S (j+1))) ∅ (dyadicGapDen j) n) :
    GroundBudgetHolds true (xorSet (groundTruncatedHybrid S g J) (S J)) ∅ (2^J) n := by
  classical
  let M i := groundBudgetMass true n (groundCutDifference S g (J+i))
  let D := groundBudgetDenom true n
  have hM (i : ℕ) (_ : i<n) : ((2:ℕ)^i*(2*(2:ℕ)^J))*M i≤D := by
    have hCoeff : (2:ℕ)^i*(2*(2:ℕ)^J)=dyadicGapDen (J+i) := by
      unfold dyadicGapDen
      rw [pow_succ,pow_add]
      ring
    rw [hCoeff]
    by_cases hN : actualGroundHybridCut g (J+i+1)≤n
    · have hh := hG (J+i) hN
      rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty] at hh
      exact (Nat.mul_le_mul_left _ (groundBudgetMass_mono_r232 true n
        (show groundCutDifference S g (J+i)⊆xorSet (S (J+i)) (S (J+i+1)) from fun {_} h => h.1))).trans hh
    · have he : M i=0 := by
        unfold M groundBudgetMass
        apply Finset.sum_eq_zero
        intro m hm
        have hn := Finset.mem_range.mp hm
        have hn' : m∉groundCutDifference S g (J+i) := fun h => hN (h.2.trans hn.le)
        simp [hn']
      simp [he]
  rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
  have hS := (groundBudgetMass_prefix_mono_r341 true n (groundTruncated_errors_covered_r343 S g J n)).trans
    (groundBudgetMass_finite_union_r343 true n (fun i => groundCutDifference S g (J+i)) n)
  exact (Nat.mul_le_mul_left _ hS).trans (dyadic_natBudget_sum_r343 D n (2^J) M hM)

theorem actualTruncated_smallAllPrefixes_r343 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (J : ℕ) : p ≤ smallAllPrefixes true (2^J) (bitsSymmDiff (actualTruncatedHybrid f x J) (f J x)) := by
  apply le_iInf
  intro n
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨g,S,r,hr,hrq,hF',hT,hG⟩ := exists_truncatedHybrid_groundPrefix_r342 f R hF x J n hq hqp
  exact ⟨r,hr,hrq,nameErrorBudget_crispPrefix_complete_r340 true (2^J) n hT
    (hF' J (le_max_left J n)) (groundTruncated_dyadicBudget_r343 S g J n hG)⟩

end SetLanguage
end JSP000933
