import JSP000930AnalyticRationalDiscs
import Mathlib.Analysis.Analytic.IsolatedZeros

open Set Filter

namespace JSP000930.Analytic

theorem exists_real_ne_in_interval {a b : ℕ → ℂ} (ha : RadiusCode a)
    (hb : RadiusCode b) (hab : a ≠ b) {l r : ℝ} (hlr : l < r) :
    ∃ x : ℝ, l < x ∧ x < r ∧ evaluate a (x : ℂ) ≠ evaluate b (x : ℂ) := by
  by_contra hnone
  have heq (x : ℝ) (hx : l < x) (hy : x < r) :
      evaluate a (x : ℂ) = evaluate b (x : ℂ) := by
    by_contra hn
    exact hnone ⟨x,hx,hy,hn⟩
  let m : ℝ := (l+r)/2
  have hl : l < m := by dsimp [m]; linarith
  have hr : m < r := by dsimp [m]; linarith
  have hacc : (m : ℂ) ∈ closure
      ({z : ℂ | evaluate a z = evaluate b z} \ {(m : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε he
    let δ := min (ε/2) ((r-m)/2)
    have hδ : 0 < δ := lt_min (by positivity) (by linarith)
    have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
    have hδr : δ < r-m := (min_le_right _ _).trans_lt (by linarith)
    let x := m+δ
    refine ⟨(x : ℂ), ⟨heq x (by dsimp [x]; linarith) (by dsimp [x]; linarith), ?_⟩, ?_⟩
    · intro hx
      have hx' : (x : ℂ) = (m : ℂ) := hx
      have : x = m := Complex.ofReal_injective hx'
      dsimp [x] at this
      linarith
    · have hdist : dist (m : ℂ) (x : ℂ) = δ := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show m-x = -δ by dsimp [x]; ring, abs_neg, abs_of_pos hδ]
      linarith
  have hall := (analytic_evaluate ha).eqOn_of_preconnected_of_mem_closure
    (analytic_evaluate hb) isPreconnected_univ (Set.mem_univ (m : ℂ)) hacc
  exact hab (evaluate_injective ha hb (funext fun z => hall (Set.mem_univ z)))

theorem exists_realInterval_finiteCertificate {a b : ℕ → ℂ}
    (ha : RadiusCode a) (hb : RadiusCode b) (hab : a ≠ b)
    {l r : ℝ} (hlr : l < r) :
    ∃ (p q : ℚ) (R A B N : ℕ) (D : RationalDisc),
      l < (p : ℝ) ∧ p < q ∧ (q : ℝ) < r ∧ 0 < D.2.2 ∧
      (∀ j : ℕ, ‖a j‖ * (R : ℝ)^j ≤ (A : ℝ)) ∧
      (∀ j : ℕ, ‖b j‖ * (R : ℝ)^j ≤ (B : ℝ)) ∧
      discSet D ⊆ finiteSeparationRegion a b R A B N ∧
      ∀ x : ℝ, (p : ℝ) ≤ x → x ≤ (q : ℝ) → (x : ℂ) ∈ discSet D := by
  obtain ⟨x,hl,hx,hn⟩ := exists_real_ne_in_interval ha hb hab hlr
  obtain ⟨R,A,B,N,D,hD,hxD,hA,hB,hsub⟩ :=
    (evaluate_ne_iff_rationalDiscFiniteCertificate ha hb (x : ℂ)).mp hn
  have hO : IsOpen ((fun u : ℝ => (u : ℂ)) ⁻¹' discSet D) :=
    Metric.isOpen_ball.preimage Complex.continuous_ofReal
  obtain ⟨ε,he,heD⟩ := Metric.isOpen_iff.mp hO x hxD
  have hlx : max l (x-ε) < x := max_lt hl (by linarith)
  have hxr : x < min r (x+ε) := lt_min hx (by linarith)
  obtain ⟨p,hpl,hpx⟩ := exists_rat_btwn hlx
  obtain ⟨q,hxq,hqr⟩ := exists_rat_btwn hxr
  have hpq : p < q := by exact_mod_cast hpx.trans hxq
  refine ⟨p,q,R,A,B,N,D,(le_max_left _ _).trans_lt hpl,hpq,
    hqr.trans_le (min_le_left _ _),hD,hA,hB,hsub,?_⟩
  intro u hp hq
  apply heD
  rw [Metric.mem_ball,Real.dist_eq]
  have h₁ := (le_max_right l (x-ε)).trans_lt hpl
  have h₂ := hqr.trans_le (min_le_right r (x+ε))
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

end JSP000930.Analytic
