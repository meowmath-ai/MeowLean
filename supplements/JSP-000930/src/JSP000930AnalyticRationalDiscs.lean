import JSP000930AnalyticTaylorTail
import Mathlib.Algebra.Order.Archimedean.Basic

open Filter Set
open scoped Topology BigOperators

namespace JSP000930.Analytic

abbrev RationalDisc := ℚ × ℚ × ℚ

noncomputable def discCenter (D : RationalDisc) : ℂ := ⟨(D.1 : ℝ), (D.2.1 : ℝ)⟩

noncomputable def discSet (D : RationalDisc) : Set ℂ := Metric.ball (discCenter D) (D.2.2 : ℝ)

theorem exists_rational_center (z : ℂ) (ε : ℝ) (he : 0 < ε) :
    ∃ (p q : ℚ), dist z (discCenter (p,q,0)) < ε := by
  obtain ⟨p,hpl,hpu⟩ := exists_rat_btwn (show z.re - ε/2 < z.re + ε/2 by linarith)
  obtain ⟨q,hql,hqu⟩ := exists_rat_btwn (show z.im - ε/2 < z.im + ε/2 by linarith)
  refine ⟨p,q, ?_⟩
  let w := z - discCenter (p,q,0)
  have hRe : |w.re| < ε/2 := by
    change |z.re - (p : ℝ)| < ε/2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hIm : |w.im| < ε/2 := by
    change |z.im - (q : ℝ)| < ε/2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hw := Complex.norm_le_abs_re_add_abs_im w
  rw [dist_eq_norm]
  change ‖w‖ < ε
  linarith

theorem exists_rationalDisc_of_open_mem {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ D : RationalDisc, 0 < D.2.2 ∧ z ∈ discSet D ∧ discSet D ⊆ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨p,q,hcenter⟩ := exists_rational_center z (ε/2) (by positivity)
  let w : ℂ := discCenter (p,q,0)
  have hd : dist z w < ε/2 := hcenter
  obtain ⟨r,hr₁,hr₂⟩ := exists_rat_btwn (show dist z w < ε - dist z w by linarith)
  have hr : 0 < r := by
    have hh : (0 : ℝ) < (r : ℝ) := dist_nonneg.trans_lt hr₁
    exact_mod_cast hh
  refine ⟨(p,q,r), hr, hr₁, ?_⟩
  intro x hx
  apply hball
  have hx' : dist x w < (r : ℝ) := hx
  have ht := dist_triangle x w z
  rw [dist_comm w z] at ht
  change dist x z < ε
  linarith

theorem continuous_partialSum_eval (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun z => partialSum a z N) := by
  have h : (fun z => partialSum a z N) =
      (FormalMultilinearSeries.ofScalars ℂ a).partialSum N := by
    funext z
    simp only [partialSum, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [h]
  exact (FormalMultilinearSeries.ofScalars ℂ a).partialSum_continuous N

def finiteSeparationRegion (a b : ℕ → ℂ) (R A B N : ℕ) : Set ℂ :=
  {w | ‖w‖ < (R : ℝ)/2 ∧
    tailBudget A N + tailBudget B N < ‖partialSum a w N - partialSum b w N‖}

theorem finiteSeparationRegion_open (a b : ℕ → ℂ) (R A B N : ℕ) :
    IsOpen (finiteSeparationRegion a b R A B N) := by
  have hp := (continuous_partialSum_eval a N).sub (continuous_partialSum_eval b N)
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const (continuous_norm.comp hp))

theorem evaluate_ne_iff_rationalDiscFiniteCertificate {a b : ℕ → ℂ}
    (ha : RadiusCode a) (hb : RadiusCode b) (z : ℂ) :
    evaluate a z ≠ evaluate b z ↔
      ∃ (R A B N : ℕ) (D : RationalDisc),
        0 < D.2.2 ∧ z ∈ discSet D ∧
        (∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (A : ℝ)) ∧
        (∀ j : ℕ, ‖b j‖ * (R : ℝ)^j ≤ (B : ℝ)) ∧
        discSet D ⊆ finiteSeparationRegion a b R A B N := by
  constructor
  · intro h
    obtain ⟨R,hR⟩ := exists_nat_gt (2 * ‖z‖)
    have hpos : 0 < R := by
      have hh : (0 : ℝ) < (R : ℝ) := (by positivity : 0 ≤ 2 * ‖z‖).trans_lt hR
      exact_mod_cast hh
    have hz : ‖z‖ < (R : ℝ)/2 := by linarith
    obtain ⟨A,hA⟩ := ha R (by omega)
    obtain ⟨B,hB⟩ := hb R (by omega)
    obtain ⟨N,hN⟩ := (eventually_partialSum_separation ha hb hA hB hz.le h).exists
    obtain ⟨D,hDp,hDz,hD⟩ := exists_rationalDisc_of_open_mem
      (finiteSeparationRegion_open a b R A B N) (show z ∈ finiteSeparationRegion a b R A B N from ⟨hz,hN⟩)
    exact ⟨R,A,B,N,D,hDp,hDz,hA,hB,hD⟩
  · rintro ⟨R,A,B,N,D,_,hz,hA,hB,hD⟩
    obtain ⟨hz',hs⟩ := hD hz
    exact evaluate_ne_of_partialSum_separation ha hb hA hB hz'.le hs

end JSP000930.Analytic
