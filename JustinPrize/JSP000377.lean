import Mathlib

open MeasureTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace JSP000377

def AvoidsIntegers (δ r : ℝ) : Prop := ∀ m : ℤ, δ ≤ |r - (m : ℝ)|

def Good (δ : ℝ) (s : Finset ℂ) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, p ≠ q → AvoidsIntegers δ (dist p q)

theorem good_separation {δ : ℝ} {s : Finset ℂ} (hs : Good δ s)
    {p q : ℂ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) :
    δ ≤ dist p q := by
  have hh := hs p hp q hq hpq 0
  simpa only [Int.cast_zero, sub_zero, abs_of_nonneg (dist_nonneg : 0 ≤ dist p q)] using hh

theorem packing (δ R : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ (s : Finset ℂ) (p : ℂ), Good δ s →
      (s.filter (fun q => dist q p < R)).card ≤ M := by
  classical
  obtain ⟨F, _, hF, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded
      (isCompact_closedBall (0 : ℂ) R).totallyBounded (δ / 2) (by linarith)
  refine ⟨hF.toFinset.card, ?_⟩
  intro s p hs
  let t := s.filter (fun q => dist q p < R)
  have hchoose (q : ↥t) : ∃ f : ↥hF.toFinset, dist (q.1 - p) f.1 < δ / 2 := by
    have hq₁ : dist q.1 p < R := (Finset.mem_filter.mp q.2).2
    have hq₂ : q.1 - p ∈ Metric.closedBall (0 : ℂ) R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hq₁.le
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp (hcover hq₂)
    obtain ⟨hfF, hfball⟩ := Set.mem_iUnion.mp hf
    exact ⟨⟨f, hF.mem_toFinset.mpr hfF⟩, Metric.mem_ball.mp hfball⟩
  let f (q : ↥t) := (hchoose q).choose
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have ha : dist (a.1 - p) (f a).1 < δ / 2 := (hchoose a).choose_spec
    have hb : dist (b.1 - p) (f b).1 < δ / 2 := (hchoose b).choose_spec
    rw [← hab] at hb
    have htri := dist_triangle (a.1 - p) (f a).1 (b.1 - p)
    have htrans : dist (a.1 - p) (b.1 - p) = dist a.1 b.1 := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rw [dist_comm (f a).1 (b.1 - p), htrans] at htri
    have hsep := good_separation hs (Finset.mem_filter.mp a.2).1
      (Finset.mem_filter.mp b.2).1 hne
    linarith
  exact Finset.card_le_card_of_injective hf

def RadialKernel (δ : ℝ) (K : ℝ → ℝ) (B a R : ℝ) : Prop :=
  0 ≤ B ∧ 0 < a ∧ 0 < R ∧
  (∀ r : ℝ, K r ≤ B) ∧
  (∀ r : ℝ, R ≤ r → AvoidsIntegers δ r → K r ≤ -(a / Real.sqrt r)) ∧
  (∀ s : Finset ℂ, 0 ≤ ∑ p ∈ s, ∑ q ∈ s, K (dist q p))

private theorem le_cancel_positive_real {a b c : ℝ} (ha : 0 < a)
    (h : a * b ≤ a * c) : b ≤ c := by
  by_contra! hn
  exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left hn ha)

theorem bound_of_kernel {δ : ℝ} (hδ : 0 < δ) {K : ℝ → ℝ} {B a R : ℝ}
    (hK : RadialKernel δ K B a R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (o : ℂ) (s : Finset ℂ),
      (∀ p ∈ s, dist p o ≤ X) → Good δ s → (s.card : ℝ) < C * Real.sqrt X := by
  classical
  obtain ⟨hB, ha, hR, hglobal, hfar, hpsd⟩ := hK
  obtain ⟨M, hM⟩ := packing δ R hδ
  let C₀ : ℝ := (M : ℝ) * (2 * B + a) / a
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro X hX o s hball hs
  have hX₀ : 0 ≤ X := by linarith
  have hsqrtX : 0 < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
  have hsqrtX₁ : 1 ≤ Real.sqrt X := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX
  let D : ℝ := 2 * Real.sqrt X
  have hD : 0 < D := by dsimp [D]; positivity
  have hD₂ : D ^ 2 = 4 * X := by
    dsimp [D]
    nlinarith only [Real.sq_sqrt hX₀]
  let t : ℝ := a / D
  have ht : 0 < t := div_pos ha hD
  have htD : t * D = a := div_mul_cancel₀ a hD.ne'
  let n : ℝ := s.card
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hrow (p : ℂ) (hp : p ∈ s) :
      (∑ q ∈ s, (K (dist q p) + t)) ≤ (M : ℝ) * (B + t) := by
    have hentry (q : ℂ) (hq : q ∈ s) :
        K (dist q p) + t ≤ if dist q p < R then B + t else 0 := by
      by_cases h : dist q p < R
      · rw [ite_eq_left h]
        exact add_le_add (hglobal (dist q p)) (le_rfl : t ≤ t)
      · rw [ite_eq_right h]
        have hRq : R ≤ dist q p := le_of_not_gt h
        have hpos : 0 < dist q p := hR.trans_le hRq
        have hne : q ≠ p := by
          intro h'
          subst q
          simp at hpos
        have hd : dist q p ≤ D ^ 2 := by
          rw [hD₂]
          have htri := dist_triangle q o p
          rw [dist_comm o p] at htri
          linarith [hball p hp, hball q hq]
        have hdiv : t ≤ a / Real.sqrt (dist q p) :=
          div_le_div_of_nonneg_left ha.le (Real.sqrt_pos.2 hpos) ((Real.sqrt_le_left hD.le).2 hd)
        linarith [hfar (dist q p) hRq (hs q hq p hp hne)]
    calc
      _ ≤ ∑ q ∈ s, (if dist q p < R then B + t else 0) := Finset.sum_le_sum hentry
      _ = ((s.filter fun q => dist q p < R).card : ℝ) * (B + t) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hM s p hs) (by linarith)
  have hsum :
      (∑ p ∈ s, ∑ q ∈ s, (K (dist q p) + t)) ≤ n * ((M : ℝ) * (B + t)) := by
    calc
      _ ≤ ∑ p ∈ s, (M : ℝ) * (B + t) := Finset.sum_le_sum hrow
      _ = _ := by simp [n, nsmul_eq_mul]
  have hsplit :
      (∑ p ∈ s, ∑ q ∈ s, (K (dist q p) + t)) =
          (∑ p ∈ s, ∑ q ∈ s, K (dist q p)) + t * n ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, n]
    ring
  rw [hsplit] at hsum
  have hmain : t * n ^ 2 ≤ n * ((M : ℝ) * (B + t)) := by linarith [hpsd s]
  have hresult : n ≤ C₀ * Real.sqrt X := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h]
      exact mul_nonneg hC₀ hsqrtX.le
    have hcancel : t * n ≤ (M : ℝ) * (B + t) := by
      apply le_cancel_positive_real h
      calc
        n * (t * n) = t * n ^ 2 := by ring
        _ ≤ _ := hmain
    have hmul : a * n ≤ (M : ℝ) * (B * D + a) := by
      calc
        a * n = (t * n) * D := by rw [← htD]; ring
        _ ≤ ((M : ℝ) * (B + t)) * D := mul_le_mul_of_nonneg_right hcancel hD.le
        _ = _ := by rw [← htD]; ring
    have hD_bound : B * D + a ≤ (2 * B + a) * Real.sqrt X := by
      have haX := mul_le_mul_of_nonneg_left hsqrtX₁ ha.le
      dsimp [D]
      nlinarith only [haX]
    apply le_cancel_positive_real ha
    calc
      a * n ≤ (M : ℝ) * (B * D + a) := hmul
      _ ≤ (M : ℝ) * ((2 * B + a) * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left hD_bound (by positivity)
      _ = a * (C₀ * Real.sqrt X) := by
        dsimp [C₀]
        field_simp [ha.ne']
        <;> ring
  change n < (C₀ + 1) * Real.sqrt X
  linarith

noncomputable def circleCos (t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (t * Real.cos θ)

private noncomputable def phase (u θ : ℝ) (z : ℂ) : ℝ :=
  u * (z.re * Real.cos θ + z.im * Real.sin θ)

theorem circleCos_le (t : ℝ) : circleCos t ≤ 2 * Real.pi := by
  unfold circleCos
  have hf : Continuous (fun θ : ℝ => Real.cos (t * Real.cos θ)) := by fun_prop
  have h₁ : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  calc
    _ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by positivity)
        (hf.intervalIntegrable _ _) (h₁.intervalIntegrable _ _)
        (fun θ _ => Real.cos_le_one _)
    _ = _ := by simp

private theorem rotation_integral (u : ℝ) (p q : ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (phase u θ q - phase u θ p)) =
      circleCos (u * dist q p) := by
  have hphase (θ : ℝ) :
      phase u θ q - phase u θ p =
        (u * ‖q - p‖) * Real.cos (θ - (q - p).arg) := by
    unfold phase
    rw [Real.cos_sub]
    calc
      _ = u * ((q - p).re * Real.cos θ + (q - p).im * Real.sin θ) := by
        simp [Complex.sub_re, Complex.sub_im]
        <;> ring
      _ = _ := by
        rw [← Complex.norm_mul_cos_arg (q - p), ← Complex.norm_mul_sin_arg (q - p)]
        ring
  rw [dist_eq_norm]
  simp_rw [hphase]
  let f (θ : ℝ) := Real.cos ((u * ‖q - p‖) * Real.cos θ)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [Real.cos_add_two_pi]
  calc
    _ = ∫ θ in (-(q - p).arg)..(2 * Real.pi + -(q - p).arg), f θ := by
      simpa only [f, sub_eq_add_neg, zero_add] using
        (intervalIntegral.integral_comp_add_right
          (a := 0) (b := 2 * Real.pi) f (-(q - p).arg))
    _ = _ := by
      simpa only [add_comm (-(q - p).arg) (2 * Real.pi), zero_add, f, circleCos]
        using hf.intervalIntegral_add_eq (-(q - p).arg) 0

theorem circleCos_psd (u : ℝ) (s : Finset ℂ) :
    0 ≤ ∑ p ∈ s, ∑ q ∈ s, circleCos (u * dist q p) := by
  classical
  let f (p q : ℂ) (θ : ℝ) := Real.cos (phase u θ q - phase u θ p)
  have hcont (p q : ℂ) : Continuous (f p q) := by
    dsimp [f, phase]
    fun_prop
  have hrow (p : ℂ) :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ q ∈ s, f p q θ) =
        ∑ q ∈ s, circleCos (u * dist q p) := by
    rw [intervalIntegral.integral_finsetSum (fun q _ => (hcont p q).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro q hq
    exact rotation_integral u p q
  have hint :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ p ∈ s, ∑ q ∈ s, f p q θ) =
        ∑ p ∈ s, ∑ q ∈ s, circleCos (u * dist q p) := by
    rw [intervalIntegral.integral_finsetSum
      (fun p _ => (continuous_finsetSum s (fun q _ => hcont p q)).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun p _ => hrow p)
  rw [← hint]
  apply intervalIntegral.integral_nonneg (by positivity)
  intro θ _
  have hid :
      (∑ p ∈ s, ∑ q ∈ s, f p q θ) =
        (∑ p ∈ s, Real.cos (phase u θ p)) ^ 2 +
          (∑ p ∈ s, Real.sin (phase u θ p)) ^ 2 := by
    simp_rw [f, Real.cos_sub, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    <;> ring
  rw [hid]
  positivity

noncomputable def freq (k : ℕ) : ℝ := 2 * Real.pi * (k : ℝ)


private theorem circleCos_quarter (t : ℝ) :
    circleCos t = 4 * (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (t * Real.cos θ)) := by
  let f (θ : ℝ) := Real.cos (t * Real.cos θ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hp : Function.Periodic f Real.pi := by
    intro θ
    simp [f, Real.cos_add_pi, Real.cos_neg]
  have hwhole : (∫ θ in Real.pi..(2 * Real.pi), f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    have he : Real.pi + Real.pi = 2 * Real.pi := by ring
    simpa only [zero_add, he] using hp.intervalIntegral_add_eq Real.pi 0
  have hreflect (θ : ℝ) : f (Real.pi - θ) = f θ := by
    simp [f, Real.cos_pi_sub, Real.cos_neg]
  have hhalf :
      (∫ θ in (Real.pi / 2)..Real.pi, f θ) =
        ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
    have he : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    simpa only [hreflect, sub_zero, he] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 2) f Real.pi).symm
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable Real.pi (2 * Real.pi))
  have hb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (Real.pi / 2)) (hc.intervalIntegrable (Real.pi / 2) Real.pi)
  rw [hwhole] at ha
  rw [hhalf] at hb
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) = 4 * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ)
  linarith only [ha, hb]

private noncomputable def phaseRoot (s : ℝ) : ℝ := Real.sqrt (1 - s ^ 2 / 4)

private theorem circleCos_quadratic (t : ℝ) :
    circleCos t = 4 * (∫ s in (0 : ℝ)..(Real.sqrt 2),
      Real.cos (t * (1 - s ^ 2 / 2)) / phaseRoot s) := by
  rw [circleCos_quarter]
  congr 1
  let f (θ : ℝ) := 2 * Real.sin (θ / 2)
  let f' (θ : ℝ) := Real.cos (θ / 2)
  let g (s : ℝ) := Real.cos (t * (1 - s ^ 2 / 2)) / phaseRoot s
  have hf' (θ : ℝ) : HasDerivAt f (f' θ) θ := by
    have hlin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ :=
      (hasDerivAt_id' θ).div_const 2
    have hh := ((Real.hasDerivAt_sin (θ / 2)).comp θ hlin).const_mul 2
    have he : 2 * (Real.cos (θ / 2) * (1 / 2)) = f' θ := by
      dsimp [f']
      ring
    simpa only [f, Function.comp_def, he] using hh
  have hf'c : Continuous f' := by dsimp [f']; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hfL : f (Real.pi / 2) = Real.sqrt 2 := by
    dsimp [f]
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
    ring
  have hp : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hcos_pos (θ : ℝ) (hθ : θ ∈ Set.uIcc 0 (Real.pi / 2)) : 0 < f' θ := by
    rw [Set.uIcc_of_le hp, Set.mem_Icc] at hθ
    dsimp [f']
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
  have hroot (θ : ℝ) (hθ : θ ∈ Set.uIcc 0 (Real.pi / 2)) : phaseRoot (f θ) = f' θ := by
    have hsq : 1 - f θ ^ 2 / 4 = f' θ ^ 2 := by
      dsimp [f, f']
      nlinarith only [Real.sin_sq_add_cos_sq (θ / 2)]
    rw [phaseRoot, hsq, Real.sqrt_sq (hcos_pos θ hθ).le]
  have hquad (θ : ℝ) : 1 - f θ ^ 2 / 2 = Real.cos θ := by
    calc
      _ = Real.cos (2 * (θ / 2)) := by
        rw [Real.cos_two_mul]
        dsimp [f]
        nlinarith only [Real.sin_sq_add_cos_sq (θ / 2)]
      _ = _ := by congr 1; ring
  have hg : ContinuousOn g (f '' Set.uIcc 0 (Real.pi / 2)) := by
    have h1 : Continuous (fun s : ℝ => Real.cos (t * (1 - s ^ 2 / 2))) := by fun_prop
    have h2 : Continuous phaseRoot := by unfold phaseRoot; fun_prop
    apply h1.continuousOn.div h2.continuousOn
    rintro _ ⟨θ, hθ, rfl⟩
    rw [hroot θ hθ]
    exact (hcos_pos θ hθ).ne'
  have hsub := intervalIntegral.integral_comp_mul_deriv'
      (fun θ _ => hf' θ) hf'c.continuousOn hg
  rw [hf0, hfL] at hsub
  change (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (t * Real.cos θ)) =
    ∫ s in (0 : ℝ)..(Real.sqrt 2), g s
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro θ hθ
  change Real.cos (t * Real.cos θ) =
    Real.cos (t * (1 - f θ ^ 2 / 2)) / phaseRoot (f θ) * f' θ
  rw [hquad, hroot θ hθ, div_mul_cancel₀ _ (hcos_pos θ hθ).ne']

private theorem varying_amplitude_error :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t →
      |(∫ s in (0 : ℝ)..(Real.sqrt 2), Real.cos (t * (1 - s ^ 2 / 2)) / phaseRoot s) -
        (∫ s in (0 : ℝ)..(Real.sqrt 2), Real.cos (t * (1 - s ^ 2 / 2)))| ≤ A / t := by
  let L : ℝ := Real.sqrt 2
  have hLpos : 0 < L := Real.sqrt_pos.2 (by norm_num)
  have hL2 : L ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let U := Set.uIcc 0 L
  have hU (s : ℝ) (hs : s ∈ U) : 0 ≤ s ∧ s ≤ L := by
    simpa only [U, Set.uIcc_of_le hLpos.le, Set.mem_Icc] using hs
  have h0U : (0 : ℝ) ∈ U := Set.left_mem_uIcc
  have hLU : L ∈ U := Set.right_mem_uIcc
  have hrootpos (s : ℝ) (hs : s ∈ U) : 0 < 1 - s ^ 2 / 4 := by
    have hb := pow_le_pow_left₀ (hU s hs).1 (hU s hs).2 2
    linarith only [hb, hL2]
  let H : ℝ → ℝ := phaseRoot
  let H' (s : ℝ) := (-s / 2) / (2 * H s)
  have hHpos (s : ℝ) (hs : s ∈ U) : 0 < H s :=
    Real.sqrt_pos.2 (hrootpos s hs)
  have hH_deriv (s : ℝ) (hs : s ∈ U) : HasDerivAt H (H' s) s := by
    have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2 / 4) (-s / 2) s := by
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have he : -(2 * s / 4) = -s / 2 := by ring
      simpa only [he] using (hsq.div_const 4).const_sub 1
    exact hbase.sqrt (hrootpos s hs).ne'
  have hHc : Continuous H := by
    change Continuous phaseRoot
    unfold phaseRoot
    exact Real.continuous_sqrt.comp (by fun_prop : Continuous (fun s : ℝ => 1 - s ^ 2 / 4))
  have hH'c : ContinuousOn H' U := by
    have hn : Continuous (fun s : ℝ => -s / 2) := by fun_prop
    have hd : Continuous (fun s => 2 * H s) := continuous_const.mul hHc
    apply hn.continuousOn.div hd.continuousOn
    exact fun s hs => mul_ne_zero (by norm_num) (hHpos s hs).ne'
  let D (s : ℝ) := 4 * H s * (1 + H s)
  let D' (s : ℝ) := 4 * H' s * (1 + H s) + 4 * H s * H' s
  have hDpos (s : ℝ) (hs : s ∈ U) : 0 < D s := by
    dsimp [D]
    have hh := hHpos s hs
    positivity
  have hD_deriv (s : ℝ) (hs : s ∈ U) : HasDerivAt D (D' s) s := by
    have hh := hH_deriv s hs
    have hc : HasDerivAt (fun x => 1 + H x) (H' s) s := hh.const_add 1
    simpa only [D, D'] using (hh.const_mul 4).fun_mul hc
  have hDc : Continuous D := by
    dsimp [D]
    exact (continuous_const.mul hHc).mul (continuous_const.add hHc)
  have hD'c : ContinuousOn D' U := by
    dsimp [D']
    exact ((continuousOn_const.mul hH'c).mul (continuousOn_const.add hHc.continuousOn)).add
      ((continuousOn_const.mul hHc.continuousOn).mul hH'c)
  let Z (s : ℝ) := s / D s
  let Z' (s : ℝ) := (D s - s * D' s) / (D s) ^ 2
  have hZderiv (s : ℝ) (hs : s ∈ U) : HasDerivAt Z (Z' s) s := by
    simpa only [Z, Z', one_mul] using
      (hasDerivAt_id' s).fun_div (hD_deriv s hs) (hDpos s hs).ne'
  have hZc : ContinuousOn Z U :=
    continuousOn_id.div hDc.continuousOn (fun s hs => (hDpos s hs).ne')
  have hZ'c : ContinuousOn Z' U :=
    (hDc.continuousOn.sub (continuousOn_id.mul hD'c)).div
      (hDc.continuousOn.pow 2) (fun s hs => pow_ne_zero 2 (hDpos s hs).ne')
  have hAeq (s : ℝ) (hs : s ∈ U) : 1 / H s - 1 = s * Z s := by
    have hsq : H s ^ 2 = 1 - s ^ 2 / 4 := Real.sq_sqrt (hrootpos s hs).le
    have hh := hHpos s hs
    dsimp [Z]
    rw [← mul_div_assoc]
    apply (eq_div_iff (hDpos s hs).ne').2
    dsimp [D]
    calc
      _ = 4 * (1 - H s ^ 2) := by field_simp [hh.ne'] <;> ring
      _ = _ := by nlinarith only [hsq]
  have hUcmp : IsCompact U := isCompact_uIcc
  have hUne : U.Nonempty := ⟨0, h0U⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hUcmp.exists_isMaxOn hUne hZc.abs
  obtain ⟨z₁, hz₁, hmax'⟩ := hUcmp.exists_isMaxOn hUne hZ'c.abs
  let M₀ := |Z z₀|
  let M₁ := |Z' z₁|
  have hm₀ (s : ℝ) (hs : s ∈ U) : |Z s| ≤ M₀ := hmax hs
  have hm₁ (s : ℝ) (hs : s ∈ U) : |Z' s| ≤ M₁ := hmax' hs
  refine ⟨2 * M₀ + M₁ * L, by dsimp [M₀, M₁]; positivity, ?_⟩
  intro t ht
  let f (s : ℝ) := Real.cos (t * (1 - s ^ 2 / 2))
  let g (s : ℝ) := Real.sin (t * (1 - s ^ 2 / 2))
  let g' (s : ℝ) := -(t * s) * f s
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg'c : Continuous g' := by dsimp [g', f]; fun_prop
  have hg_deriv (s : ℝ) : HasDerivAt g (g' s) s := by
    have hinner : HasDerivAt (fun x : ℝ => t * (1 - x ^ 2 / 2)) (-(t * s)) s := by
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have he : t * -(2 * s / 2) = -(t * s) := by ring
      simpa only [he] using ((hsq.div_const 2).const_sub 1).const_mul t
    have he : Real.cos (t * (1 - s ^ 2 / 2)) * (-(t * s)) = g' s := by
      dsimp only [g', f]
      ring
    simpa only [g, Function.comp_def, he] using
      (Real.hasDerivAt_sin (t * (1 - s ^ 2 / 2))).comp s hinner
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s hs => hZderiv s hs) (fun s _ => hg_deriv s)
    (hZ'c.intervalIntegrable) (hg'c.intervalIntegrable 0 L)
  have hfcH : ContinuousOn (fun s => f s / H s) U :=
    hfc.continuousOn.div hHc.continuousOn (fun s hs => (hHpos s hs).ne')
  have hconvert :
      (∫ s in (0 : ℝ)..L, Z s * g' s) =
        -t * ((∫ s in (0 : ℝ)..L, f s / H s) - ∫ s in (0 : ℝ)..L, f s) := by
    rw [← intervalIntegral.integral_sub hfcH.intervalIntegrable (hfc.intervalIntegrable 0 L),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change Z s * (-(t * s) * f s) = -t * (f s / H s - f s)
    have hh : (1 / H s - 1) * f s = f s / H s - f s := by ring
    rw [← hh, hAeq s hs]
    ring
  have hprod (s : ℝ) (hs : s ∈ U) : |Z s * g s| ≤ M₀ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (hm₀ s hs)
  have hInt :
      |∫ s in (0 : ℝ)..L, Z' s * g s| ≤ M₁ * L := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := L) (C := M₁) (f := fun s => Z' s * g s) (fun s hs => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans
         (hm₁ s (Set.uIoc_subset_uIcc hs)))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hLpos] using hh
  have hBound :
      |(Z L * g L - Z 0 * g 0) - ∫ s in (0 : ℝ)..L, Z' s * g s| ≤ 2 * M₀ + M₁ * L := by
    have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le a b
    linarith only [htriangle (Z L * g L - Z 0 * g 0) (∫ s in (0 : ℝ)..L, Z' s * g s),
      htriangle (Z L * g L) (Z 0 * g 0), hprod L hLU, hprod 0 h0U, hInt]
  rw [← hparts, hconvert, abs_mul, abs_neg, abs_of_pos ht] at hBound
  apply (le_div_iff₀ ht).2
  simpa only [mul_comm] using hBound


private noncomputable def gaussian (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-b * (x : ℂ) ^ 2)

private theorem gaussian_continuous (b : ℂ) : Continuous (gaussian b) := by
  unfold gaussian
  fun_prop

private theorem gaussian_norm_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖gaussian b x‖ ≤ 1 := by
  rw [gaussian, norm_cexp_neg_mul_sq, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _))

private theorem inverse_sq_integral {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Ioi L) ∧
      (∫ x in Set.Ioi L, (x ^ 2)⁻¹) = L⁻¹ := by
  have he (x : ℝ) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_ofNat, inv_pow]
  have h := (show (-2 : ℝ) < -1 by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [he] using integrableOn_Ioi_rpow_of_lt h hL
  · have hi := integral_Ioi_rpow_of_lt h hL
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at hi
    simpa [he] using hi

private theorem gaussian_tail_bound {b : ℂ} (hb : 0 < b.re) {L : ℝ} (hL : 0 < L) :
    ‖∫ x in Set.Ioi L, gaussian b x‖ ≤ 1 / (‖b‖ * L) := by
  have hbne : b ≠ 0 := Complex.ne_zero_of_re_pos hb
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  let c : ℝ := (2 * ‖b‖)⁻¹
  let g (x : ℝ) := -gaussian b x / (2 * b * (x : ℂ))
  let rem (x : ℝ) := gaussian b x / (2 * b * (x : ℂ) ^ 2)
  have hbn (x : ℝ) : ‖gaussian b x‖ ≤ 1 := gaussian_norm_le_one hb.le x
  have hgn (x : ℝ) (hx : 0 < x) : ‖g x‖ ≤ c * x⁻¹ := by
    dsimp only [g]
    rw [norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    calc
      _ ≤ 1 / (2 * ‖b‖ * x) := div_le_div_of_nonneg_right (hbn x) (by positivity)
      _ = _ := by dsimp [c]; field_simp [hx.ne', hbpos.ne'] <;> ring
  have hrn (x : ℝ) (hx : 0 < x) : ‖rem x‖ ≤ c * (x ^ 2)⁻¹ := by
    dsimp only [rem]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_two, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    calc
      _ ≤ 1 / (2 * ‖b‖ * x ^ 2) := div_le_div_of_nonneg_right (hbn x) (by positivity)
      _ = _ := by dsimp [c]; field_simp [hx.ne', hbpos.ne'] <;> ring
  have hgderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt g (gaussian b x + rem x) x := by
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hcderiv : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hfderiv : HasDerivAt (gaussian b) (-2 * b * (x : ℂ) * gaussian b x) x := by
      convert ((hcderiv.fun_pow 2).const_mul (-b)).cexp using 1
      all_goals first
      | rfl
      | (funext y; simp only [gaussian, neg_mul])
      | (simp [gaussian] <;> ring)
    have hden : HasDerivAt (fun s : ℝ => 2 * b * (s : ℂ)) (2 * b) x := by
      simpa using hcderiv.const_mul (2 * b)
    have hdenne : (2 : ℂ) * b * (x : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hbne) hxC
    convert hfderiv.neg.div hden hdenne using 1
    <;> dsimp [g, rem]
    <;> field_simp [hbne, hxC]
    <;> ring
  have hg_lim : Tendsto g atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have hlimit : Tendsto (fun x : ℝ => c * x⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := c)).mul tendsto_inv_atTop_zero
    apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg (g x))) ?_ hlimit
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hgn x hx
  have hf_int : IntegrableOn (gaussian b) (Set.Ioi L) := integrable_cexp_neg_mul_sq hb |>.integrableOn
  obtain ⟨hinv, hI⟩ := inverse_sq_integral hL
  have hmaj : IntegrableOn (fun x : ℝ => c * (x ^ 2)⁻¹) (Set.Ioi L) := Integrable.const_mul hinv c
  have hrem_norm : ∀ᵐ x ∂(volume.restrict (Set.Ioi L)), ‖rem x‖ ≤ c * (x ^ 2)⁻¹ := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact hrn x (hL.trans hx)
  have hrem_meas : Measurable rem := by
    dsimp [rem, gaussian]
    first | fun_prop | measurability
  have hrem_int : IntegrableOn rem (Set.Ioi L) :=
    Integrable.mono' hmaj hrem_meas.aestronglyMeasurable hrem_norm
  have hparts :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx => hgderiv x (hL.trans_le hx)) (hf_int.add hrem_int) hg_lim
  rw [integral_add hf_int hrem_int, zero_sub] at hparts
  have hrem_bound : ‖∫ x in Set.Ioi L, rem x‖ ≤ c * L⁻¹ := by
    calc
      _ ≤ ∫ x in Set.Ioi L, ‖rem x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi L, c * (x ^ 2)⁻¹ := integral_mono_ae (Integrable.norm hrem_int) hmaj hrem_norm
      _ = _ := by rw [integral_const_mul, hI]
  have hexpr : (∫ x in Set.Ioi L, gaussian b x) = -g L - ∫ x in Set.Ioi L, rem x :=
    eq_sub_of_add_eq hparts
  calc
    _ = ‖-g L - ∫ x in Set.Ioi L, rem x‖ := by rw [hexpr]
    _ ≤ ‖-g L‖ + ‖∫ x in Set.Ioi L, rem x‖ := norm_sub_le _ _
    _ ≤ c * L⁻¹ + c * L⁻¹ := by rw [norm_neg]; exact add_le_add (hgn L hL) hrem_bound
    _ = _ := by dsimp [c]; field_simp [hL.ne', hbpos.ne'] <;> ring

private noncomputable def imFreq (t : ℝ) : ℂ := (↑(t / 2) : ℂ) * Complex.I

private noncomputable def dampedFreq (t ε : ℝ) : ℂ := (ε : ℂ) + imFreq t

private theorem imFreq_norm (t : ℝ) (ht : 0 < t) : ‖imFreq t‖ = t / 2 := by
  unfold imFreq
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg (half_pos ht).le]

private theorem dampedFreq_norm_lower (t ε : ℝ) :
    t / 2 ≤ ‖dampedFreq t ε‖ := by
  simpa [dampedFreq, imFreq, Complex.mul_im] using Complex.im_le_norm (dampedFreq t ε)

private theorem gaussian_value_boundary (t : ℝ) (ht : 0 < t) :
    (Real.pi : ℂ) / imFreq t ∈ Complex.slitPlane ∧
    ((Real.pi : ℂ) / imFreq t) ^ (1 / 2 : ℂ) / 2 =
      (↑(Real.sqrt (Real.pi / (2 * t))) : ℂ) *
        Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I) := by
  let R := Real.sqrt (Real.pi / (2 * t))
  have hRpos : 0 < R := by dsimp [R]; positivity
  let w := Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I)
  let z := (↑(2 * R) : ℂ) * w
  have hR₂ : (2 * R) ^ 2 = 2 * Real.pi / t := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [ht.ne']
    <;> ring
  have hw₂ : w ^ 2 = -Complex.I := by
    dsimp [w]
    rw [← Complex.exp_nat_mul]
    have he : (↑(2 : ℕ) : ℂ) * ((↑(-Real.pi / 4) : ℂ) * Complex.I) =
        (↑(-Real.pi / 2) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_ofReal_mul_I]
    simp [neg_div, Real.cos_neg, Real.sin_neg]
  have hz₂ : z ^ 2 = (↑(2 * Real.pi / t) : ℂ) * (-Complex.I) := by
    dsimp only [z]
    rw [mul_pow, ← Complex.ofReal_pow, hR₂, hw₂]
  have hbne : imFreq t ≠ 0 := norm_pos_iff.mp (by rw [imFreq_norm t ht]; positivity)
  have hzvalue : z ^ 2 = (Real.pi : ℂ) / imFreq t := by
    apply (eq_div_iff hbne).2
    rw [hz₂]
    dsimp [imFreq]
    calc
      _ = (↑(2 * Real.pi / t) : ℂ) * (↑(t / 2) : ℂ) * (-(Complex.I ^ 2)) := by ring
      _ = _ := by
        rw [Complex.I_sq, neg_neg, mul_one, ← Complex.ofReal_mul]
        congr 1
        field_simp [ht.ne']
        <;> ring
  have hZre : 0 < z.re := by
    dsimp [z, w]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_im,
      zero_mul, sub_zero, neg_div, Real.cos_neg, Real.cos_pi_div_four]
    positivity
  refine ⟨?_, ?_⟩
  · rw [← hzvalue, hz₂, Complex.mem_slitPlane_iff]
    right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.neg_im, Complex.I_im,
      Complex.ofReal_im, zero_mul, add_zero, mul_neg, mul_one, neg_ne_zero]
    positivity
  · rw [← hzvalue, show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, Complex.sq_cpow_two_inv hZre]
    change z / 2 = (R : ℂ) * w
    dsimp [z]
    push_cast
    ring

private theorem finite_gaussian_damping_bound (t ε L : ℝ) (hε : 0 ≤ ε) (hL : 0 ≤ L) :
    ‖(∫ x in (0 : ℝ)..L, gaussian (dampedFreq t ε) x) -
      ∫ x in (0 : ℝ)..L, gaussian (imFreq t) x‖ ≤ ε * L ^ 3 := by
  rw [← intervalIntegral.integral_sub ((gaussian_continuous _).intervalIntegrable 0 L)
    ((gaussian_continuous _).intervalIntegrable 0 L)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := L) (C := ε * L ^ 2)
      (f := fun x => gaussian (dampedFreq t ε) x - gaussian (imFreq t) x) (fun x hx => by
        have hx' : 0 < x ∧ x ≤ L := by
          simpa only [Set.uIoc_of_le hL, Set.mem_Ioc] using hx
        let y : ℝ := -ε * x ^ 2
        have hy : y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (sq_nonneg _)
        have hf : gaussian (dampedFreq t ε) x =
            (↑(Real.exp y) : ℂ) * gaussian (imFreq t) x := by
          unfold gaussian dampedFreq
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          congr 1
          dsimp [y]
          push_cast
          ring
        have hnorm : ‖gaussian (imFreq t) x‖ = 1 := by
          rw [gaussian, norm_cexp_neg_mul_sq]
          simp [imFreq, Complex.mul_re]
        have hl : Real.exp y ≤ 1 := by simpa using Real.exp_le_exp.mpr hy
        calc
          _ = ‖((↑(Real.exp y) : ℂ) - 1) * gaussian (imFreq t) x‖ := by rw [hf, sub_mul, one_mul]
          _ = 1 - Real.exp y := by
            rw [norm_mul, hnorm, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
            ring
          _ ≤ ε * x ^ 2 := by dsimp [y]; linarith only [Real.add_one_le_exp (-ε * x ^ 2)]
          _ ≤ ε * L ^ 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hx'.1.le hx'.2 2) hε)
  rw [sub_zero, abs_of_nonneg hL] at hh
  simpa [pow_succ, mul_assoc] using hh

private theorem fresnel_complex_bound (t L : ℝ) (ht : 0 < t) (hL : 0 < L) :
    ‖(∫ x in (0 : ℝ)..L, gaussian (imFreq t) x) -
      (↑(Real.sqrt (Real.pi / (2 * t))) : ℂ) *
        Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I)‖ ≤ 2 / (t * L) := by
  let f := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  haveI : f.NeBot := by dsimp [f]; infer_instance
  have hε : ∀ᶠ ε in f, (0 : ℝ) < ε := by
    exact self_mem_nhdsWithin
  let A (ε : ℝ) := ∫ x in (0 : ℝ)..L, gaussian (dampedFreq t ε) x
  let A₀ := ∫ x in (0 : ℝ)..L, gaussian (imFreq t) x
  have hA : Tendsto A f (𝓝 A₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hT : Tendsto (fun ε : ℝ => ε * L ^ 3) f (𝓝 0) := by
      have hId : Tendsto (fun ε : ℝ => ε) f (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_mul] using hId.mul (tendsto_const_nhds (x := L ^ 3))
    apply squeeze_zero' (Eventually.of_forall (fun ε => norm_nonneg (A ε - A₀))) ?_ hT
    filter_upwards [hε] with ε he
    exact finite_gaussian_damping_bound t ε L he.le hL.le
  let G (ε : ℝ) := ((Real.pi : ℂ) / dampedFreq t ε) ^ (1 / 2 : ℂ) / 2
  let G₀ := (↑(Real.sqrt (Real.pi / (2 * t))) : ℂ) *
    Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I)
  obtain ⟨hslit, hG₀⟩ := gaussian_value_boundary t ht
  have hG : Tendsto G f (𝓝 G₀) := by
    have hc : Continuous (dampedFreq t) := by
      change Continuous (fun ε : ℝ => (ε : ℂ) + imFreq t)
      exact Complex.continuous_ofReal.add continuous_const
    have hzero : dampedFreq t 0 = imFreq t := by simp [dampedFreq]
    have hbne : dampedFreq t 0 ≠ 0 := by
      rw [hzero]
      exact norm_pos_iff.mp (by rw [imFreq_norm t ht]; positivity)
    have hdiv : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) / dampedFreq t ε) 0 :=
      continuousAt_const.div hc.continuousAt hbne
    have hslit' : (Real.pi : ℂ) / dampedFreq t 0 ∈ Complex.slitPlane := by simpa [hzero] using hslit
    have hcont : ContinuousAt G 0 := by
      exact (hdiv.cpow continuousAt_const hslit').div_const _
    have h0 : G 0 = G₀ := by simpa [G, G₀, hzero] using hG₀
    rw [← h0]
    exact hcont.continuousWithinAt
  have htail : ∀ᶠ ε in f, ‖A ε - G ε‖ ≤ 2 / (t * L) := by
    filter_upwards [hε] with ε he
    let b := dampedFreq t ε
    have hb : 0 < b.re := by simpa [b, dampedFreq, imFreq, Complex.mul_re] using he
    have hh := intervalIntegral.integral_interval_add_Ioi'
      ((gaussian_continuous b).intervalIntegrable 0 L)
      ((integrable_cexp_neg_mul_sq hb).integrableOn (s := Set.Ioi L))
    rw [show (∫ x in Set.Ioi (0 : ℝ), gaussian b x) = G ε by
      exact integral_gaussian_complex_Ioi hb] at hh
    have heq : A ε - G ε = -(∫ x in Set.Ioi L, gaussian b x) := by
      change (∫ x in (0 : ℝ)..L, gaussian b x) - G ε = _
      rw [← hh]
      abel
    rw [heq, norm_neg]
    have hnum : (1 : ℝ) / ((t / 2) * L) = 2 / (t * L) := by field_simp [ht.ne', hL.ne'] <;> ring
    calc
      _ ≤ 1 / (‖b‖ * L) := gaussian_tail_bound hb hL
      _ ≤ 1 / ((t / 2) * L) := div_le_div_of_nonneg_left (by norm_num)
        (by positivity) (mul_le_mul_of_nonneg_right (dampedFreq_norm_lower t ε) hL.le)
      _ = _ := hnum
  exact le_of_tendsto (hA.sub hG).norm htail

private theorem truncated_fresnel_error (t : ℝ) (ht : 0 < t) :
    |(∫ s in (0 : ℝ)..(Real.sqrt 2), Real.cos (t * (1 - s ^ 2 / 2))) -
      Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4)| ≤
        (2 / Real.sqrt 2) / t := by
  let L := Real.sqrt 2
  have hL : 0 < L := Real.sqrt_pos.2 (by norm_num)
  let R := Real.sqrt (Real.pi / (2 * t))
  let u := Complex.exp ((t : ℂ) * Complex.I)
  let A := ∫ x in (0 : ℝ)..L, gaussian (imFreq t) x
  let Z := (R : ℂ) * Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := by simp [u]
  have hA :
      (∫ s in (0 : ℝ)..L, Real.cos (t * (1 - s ^ 2 / 2))) = (u * A).re := by
    dsimp only [A]
    rw [← intervalIntegral.integral_const_mul]
    have hc : Continuous (fun s : ℝ => u * gaussian (imFreq t) s) :=
      continuous_const.mul (gaussian_continuous _)
    have hre :
        (∫ s in (0 : ℝ)..L, (u * gaussian (imFreq t) s).re) =
          (∫ s in (0 : ℝ)..L, u * gaussian (imFreq t) s).re := by
      simpa only [RCLike.re_to_complex] using
        intervalIntegral.intervalIntegral_re (hc.intervalIntegrable (μ := volume) 0 L)
    rw [← hre]
    apply intervalIntegral.integral_congr
    intro s hs
    change _ = (u * gaussian (imFreq t) s).re
    dsimp only [u, gaussian, imFreq]
    rw [← Complex.exp_add]
    have he : (t : ℂ) * Complex.I + -((↑(t / 2) : ℂ) * Complex.I) * (s : ℂ) ^ 2 =
        Complex.ofReal (t * (1 - s ^ 2 / 2)) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_ofReal_mul_I_re]
  have hZ : (u * Z).re = R * Real.cos (t - Real.pi / 4) := by
    dsimp only [u, Z]
    rw [mul_left_comm, ← Complex.exp_add]
    have he : (t : ℂ) * Complex.I + (↑(-Real.pi / 4) : ℂ) * Complex.I =
        (↑(t - Real.pi / 4) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  change |(∫ s in (0 : ℝ)..L, Real.cos (t * (1 - s ^ 2 / 2))) -
    R * Real.cos (t - Real.pi / 4)| ≤ (2 / L) / t
  rw [hA, ← hZ, ← Complex.sub_re, ← mul_sub]
  calc
    _ ≤ ‖u * (A - Z)‖ := Complex.abs_re_le_norm _
    _ = ‖A - Z‖ := by rw [norm_mul, hu, one_mul]
    _ ≤ 2 / (t * L) := fresnel_complex_bound t L ht hL
    _ = _ := by field_simp [ht.ne', hL.ne'] <;> ring

theorem circleCos_scaled_error :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ k : ℕ, 0 < k → ∀ r : ℝ, 0 < r →
      Real.sqrt (k : ℝ) * Real.sqrt r * circleCos (freq k * r) ≤
        2 * Real.cos (freq k * r - Real.pi / 4) + E / Real.sqrt r := by
  obtain ⟨A, hA, hAmp⟩ := varying_amplitude_error
  let C : ℝ := A + 2 / Real.sqrt 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let E : ℝ := 2 * C / Real.pi
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro k hk r hr
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hk₀
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  let v := Real.sqrt (k : ℝ) * Real.sqrt r
  have hv : 0 < v := mul_pos hsk hsr
  let t := freq k * r
  have ht : 0 < t := by dsimp [t, freq]; positivity
  have htv : t = (2 * Real.pi) * v ^ 2 := by
    dsimp [t, freq, v]
    rw [mul_pow, Real.sq_sqrt hk₀.le, Real.sq_sqrt hr.le]
    ring
  have hJ : circleCos t ≤
      4 * (Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4)) + 4 * C / t := by
    rw [circleCos_quadratic]
    have h1 := (le_abs_self _).trans (hAmp t ht)
    have h2 := (le_abs_self _).trans (truncated_fresnel_error t ht)
    have hh :
        (∫ s in (0 : ℝ)..(Real.sqrt 2), Real.cos (t * (1 - s ^ 2 / 2)) / phaseRoot s) ≤
          Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4) + C / t := by
      dsimp [C]
      rw [add_div]
      linarith only [h1, h2]
    calc
      _ ≤ 4 * (Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4) + C / t) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hlead : v * Real.sqrt (Real.pi / (2 * t)) = 1 / 2 := by
    calc
      _ = Real.sqrt (v ^ 2 * (Real.pi / (2 * t))) := by
        rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv.le]
      _ = Real.sqrt (1 / 4) := by
        congr 1
        rw [htv]
        field_simp [Real.pi_ne_zero, hv.ne']
        <;> ring
      _ = _ := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hrem : v * (4 * C / t) = E / v := by
    rw [htv]
    dsimp [E]
    field_simp [Real.pi_ne_zero, hv.ne']
    <;> ring
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hsk₁ : 1 ≤ Real.sqrt (k : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk₁
  have hvge : Real.sqrt r ≤ v := by
    dsimp [v]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsk₁ hsr.le
  have hrem' : E / v ≤ E / Real.sqrt r := div_le_div_of_nonneg_left hE hsr hvge
  change v * circleCos t ≤ 2 * Real.cos (t - Real.pi / 4) + E / Real.sqrt r
  calc
    _ ≤ v * (4 * (Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4)) + 4 * C / t) :=
      mul_le_mul_of_nonneg_left hJ hv.le
    _ = 2 * Real.cos (t - Real.pi / 4) + E / v := by
      rw [mul_add, hrem, show v * (4 * (Real.sqrt (Real.pi / (2 * t)) * Real.cos (t - Real.pi / 4))) =
        4 * (v * Real.sqrt (Real.pi / (2 * t))) * Real.cos (t - Real.pi / 4) by ring, hlead]
      ring
    _ ≤ _ := add_le_add le_rfl hrem'

private noncomputable def evalNN (P : Polynomial NNReal) (z : ℂ) : ℂ :=
  P.eval₂ (Complex.ofRealHom.comp NNReal.toRealHom) z

private noncomputable def geometricPoly (s : NNReal) (N : ℕ) : Polynomial NNReal :=
  ∑ k ∈ Finset.range N, Polynomial.monomial (k + 1) (s ^ (k + 1))

private theorem eval_geometricPoly (s : NNReal) (N : ℕ) (z : ℂ) :
    evalNN (geometricPoly s N) z =
      ∑ k ∈ Finset.range N, (((s : ℝ) : ℂ) * z) ^ (k + 1) := by
  simp [evalNN, geometricPoly, Polynomial.eval₂_finsetSum, mul_pow]

private theorem geometricPoly_coeff_zero (s : NNReal) (N : ℕ) :
    (geometricPoly s N).coeff 0 = 0 := by
  simp [geometricPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

private theorem small_power {r ε : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hε : 0 < ε) :
    ∃ n : ℕ, r ^ n < ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁
  have he := ht.eventually (gt_mem_nhds hε)
  exact he.exists

private theorem exists_arc_polynomial (d : ℝ) (hd : 0 < d) (hd₁ : d ≤ 1) :
    ∃ P : Polynomial NNReal, P.coeff 0 = 1 ∧
      ∀ z : ℂ, ‖z‖ = 1 → z.re ≤ 1 - d → ‖evalNN P z‖ ≤ 1 / 8 := by
  let s : ℝ := 1 - d / 2
  have hs_half : 1 / 2 ≤ s := by dsimp [s]; linarith
  have hs₀ : 0 < s := by linarith
  have hs₁ : s < 1 := by dsimp [s]; linarith
  let η : ℝ := d / 32
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN⟩ := small_power hs₀.le hs₁ (mul_pos hη (sub_pos.mpr hs₁))
  have hN' : s ^ (N + 1) < η * (1 - s) := by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg hs₀.le _) hs₁.le).trans_lt hN
  let sPos : NNReal := ⟨s, hs₀.le⟩
  let F := geometricPoly sPos N
  have hF (z : ℂ) (hz : ‖z‖ = 1) (hzre : z.re ≤ 1 - d) :
      (evalNN F z).re ≤ -η ∧ ‖evalNN F z‖ ≤ (N : ℝ) := by
    let ξ : ℂ := (s : ℂ) * z
    let S : ℂ := ∑ k ∈ Finset.range N, ξ ^ (k + 1)
    have hFS : evalNN F z = S := eval_geometricPoly sPos N z
    have hξ : ‖ξ‖ = s := by
      change ‖(s : ℂ) * z‖ = s
      rw [Complex.norm_mul, Complex.norm_of_nonneg hs₀.le, hz, mul_one]
    have hξre : ξ.re = s * z.re := by simp [ξ, Complex.mul_re]
    have hdenlo : 1 - s ≤ ‖(1 : ℂ) - ξ‖ := by
      simpa [hξ] using norm_sub_norm_le (1 : ℂ) ξ
    have hdenhi : ‖(1 : ℂ) - ξ‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) ξ
      rw [norm_one, hξ] at h
      linarith
    have hdenpos : 0 < ‖(1 : ℂ) - ξ‖ := (sub_pos.mpr hs₁).trans_le hdenlo
    have hdenne : (1 : ℂ) - ξ ≠ 0 := norm_pos_iff.mp hdenpos
    have hden4 : Complex.normSq (1 - ξ) ≤ 4 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hdenhi)
        (show 0 ≤ 2 + ‖(1 : ℂ) - ξ‖ by positivity)]
    have hdenSqPos : 0 < Complex.normSq (1 - ξ) := Complex.normSq_pos.mpr hdenne
    have hξsq : ξ.re * ξ.re + ξ.im * ξ.im = s ^ 2 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hξ]
    have hnum : ξ.re - s ^ 2 ≤ -(d / 4) := by
      calc
        _ = s * z.re - s * s := by rw [hξre]; ring
        _ ≤ s * (1 - d) - s * s :=
          sub_le_sub (mul_le_mul_of_nonneg_left hzre hs₀.le) le_rfl
        _ = -(s * (d / 2)) := by dsimp [s]; ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right hs_half (show 0 ≤ d / 2 by positivity)
          linarith only [hh]
    let G := ξ / (1 - ξ)
    have hG : G.re ≤ -(d / 16) := by
      change (ξ / (1 - ξ)).re ≤ -(d / 16)
      rw [Complex.div_re, ← add_div, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, zero_sub]
      have hnum' : ξ.re * (1 - ξ.re) + ξ.im * -ξ.im = ξ.re - s ^ 2 := by
        nlinarith only [hξsq]
      rw [hnum']
      apply (div_le_iff₀ hdenSqPos).2
      have hh := mul_le_mul_of_nonneg_left hden4 (show 0 ≤ d / 16 by positivity)
      nlinarith only [hnum, hh]
    have hS : S = (∑ k ∈ Finset.range N, ξ ^ k) * ξ := by
      dsimp [S]
      simp only [pow_succ, Finset.sum_mul]
    have hSprod : S * (1 - ξ) = ξ - ξ ^ (N + 1) := by
      rw [hS, mul_right_comm, geom_sum_mul_neg, pow_succ]
      ring
    have htail : G - S = ξ ^ (N + 1) / (1 - ξ) := by
      apply (eq_div_iff hdenne).2
      dsimp [G]
      rw [sub_mul, div_mul_cancel₀ _ hdenne, hSprod]
      ring
    have htailb : ‖G - S‖ ≤ η := by
      rw [htail, norm_div, norm_pow, hξ]
      apply (div_le_iff₀ hdenpos).2
      exact hN'.le.trans (mul_le_mul_of_nonneg_left hdenlo hη.le)
    have hdiff : (S - G).re ≤ η := by
      have hn : ‖S - G‖ ≤ η := by rw [norm_sub_rev]; exact htailb
      exact (Complex.re_le_norm _).trans hn
    have hSre : S.re ≤ -η := by
      rw [Complex.sub_re] at hdiff
      dsimp only [η] at hdiff ⊢
      linarith only [hdiff, hG]
    rw [hFS]
    refine ⟨hSre, ?_⟩
    dsimp [S]
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖ξ ^ (k + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_pow, hξ]
        exact pow_le_one₀ hs₀.le hs₁.le
      _ = _ := by simp
  let q : ℝ := η / ((N : ℝ) ^ 2 + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqeq : q * ((N : ℝ) ^ 2 + 1) = η := div_mul_cancel₀ η (by positivity)
  have hqprod : q ^ 2 * (N : ℝ) ^ 2 ≤ q * η := by
    rw [← hqeq]
    nlinarith only [sq_nonneg q]
  let ρ : ℝ := Real.sqrt (1 - q * η)
  have hρ₀ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ₁ : ρ < 1 :=
    (Real.sqrt_lt' (by norm_num)).2 (by nlinarith only [mul_pos hq hη])
  obtain ⟨L, hL⟩ := small_power hρ₀ hρ₁ (by norm_num : 0 < (1 / 8 : ℝ))
  let qPos : NNReal := ⟨q, hq.le⟩
  let P : Polynomial NNReal := (1 + Polynomial.C qPos * F) ^ L
  refine ⟨P, ?_, ?_⟩
  · have hc : Polynomial.constantCoeff F = 0 := geometricPoly_coeff_zero sPos N
    change Polynomial.constantCoeff ((1 + Polynomial.C qPos * F) ^ L) = 1
    simp only [map_pow, map_add, map_one, map_mul, hc, mul_zero, add_zero, one_pow]
  · intro z hz hzre
    obtain ⟨hRe, hNorm⟩ := hF z hz hzre
    let u := evalNN F z
    have hexp : ‖(1 : ℂ) + (q : ℂ) * u‖ ^ 2 =
        1 + 2 * q * u.re + q ^ 2 * ‖u‖ ^ 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      <;> ring
    have hRe' : 2 * q * u.re ≤ 2 * q * (-η) :=
      mul_le_mul_of_nonneg_left hRe (by positivity)
    have hNorm' : q ^ 2 * ‖u‖ ^ 2 ≤ q ^ 2 * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hNorm 2) (sq_nonneg _)
    have hH : ‖(1 : ℂ) + (q : ℂ) * u‖ ≤ ρ := by
      apply Real.le_sqrt_of_sq_le
      rw [hexp]
      linarith only [hRe', hNorm', hqprod]
    have hval : evalNN P z = ((1 : ℂ) + (q : ℂ) * u) ^ L := by
      simp only [P, u, evalNN, Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_one,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.comp_apply] <;> rfl
    rw [hval, norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hH L).trans hL.le

private theorem cos_gap {δ r : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1 / 4)
    (hr : AvoidsIntegers δ r) : Real.cos (2 * Real.pi * r) ≤ Real.cos (2 * Real.pi * δ) := by
  let x := Int.fract r
  have hx₀ : 0 ≤ x := Int.fract_nonneg r
  have hx₁ : x < 1 := Int.fract_lt_one r
  have hxlo : δ ≤ x := by
    have hh := hr ⌊r⌋
    change δ ≤ |x| at hh
    rwa [abs_of_nonneg hx₀] at hh
  have hxhi : δ ≤ 1 - x := by
    have hh := hr (⌊r⌋ + 1)
    push_cast at hh
    have he : r - ((⌊r⌋ : ℤ) : ℝ) - 1 = x - 1 := rfl
    rw [← sub_sub, he, abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at hh
    linarith
  have hcos : Real.cos (2 * Real.pi * r) = Real.cos (2 * Real.pi * x) := by
    have he : 2 * Real.pi * r = 2 * Real.pi * x + ((⌊r⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
      change 2 * Real.pi * r =
        2 * Real.pi * (r - ((⌊r⌋ : ℤ) : ℝ)) + ((⌊r⌋ : ℤ) : ℝ) * (2 * Real.pi)
      ring
    rw [he, Real.cos_add_int_mul_two_pi]
  rw [hcos]
  by_cases hhalf : x ≤ 1 / 2
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by nlinarith only [mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le])
      (mul_le_mul_of_nonneg_left hxlo (by positivity))
  · have he : 2 * Real.pi * x = 2 * Real.pi - 2 * Real.pi * (1 - x) := by ring
    rw [he, Real.cos_two_pi_sub]
    have hh : 1 - x ≤ 1 / 2 := by linarith
    have hpi : 2 * Real.pi * (1 - x) ≤ Real.pi := by
      nlinarith only [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi
      (mul_le_mul_of_nonneg_left hxhi (by positivity))

theorem sign_polynomial (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset ℕ, ∃ c : ℕ → ℝ,
      (∀ k ∈ F, 0 < k ∧ 0 ≤ c k) ∧
      (∀ r : ℝ, AvoidsIntegers δ r →
        (∑ k ∈ F, c k * Real.cos (freq k * r - Real.pi / 4)) ≤ -(1 / 2 : ℝ)) := by
  classical
  let δ' := min δ (1 / 4)
  have hδ'₀ : 0 < δ' := lt_min_iff.mpr ⟨hδ, by norm_num⟩
  have hδ'₁ : δ' ≤ 1 / 4 := min_le_right _ _
  have hb₀ : 0 < 2 * Real.pi * δ' := by positivity
  have hb₁ : 2 * Real.pi * δ' ≤ Real.pi / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hδ'₁ Real.pi_pos.le]
  let d := 1 - Real.cos (2 * Real.pi * δ')
  have hd : 0 < d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      (show 2 * Real.pi * δ' ≤ Real.pi by linarith [Real.pi_pos]) hb₀
    dsimp [d]
    exact sub_pos.mpr (by simpa using hh)
  have hd₁ : d ≤ 1 := by
    have hh := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hb₁
    dsimp [d]
    linarith
  obtain ⟨P, hP₀, hP⟩ := exists_arc_polynomial d hd hd₁
  let F := P.support.erase 0
  let c (k : ℕ) : ℝ := P.coeff k
  have hmem0 : 0 ∈ P.support := Polynomial.mem_support_iff.mpr (by simp [hP₀])
  refine ⟨F, c, ?_, ?_⟩
  · intro k hk
    exact ⟨Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hk), NNReal.coe_nonneg _⟩
  · intro r hr
    let z := Complex.exp ((↑(2 * Real.pi * r) : ℂ) * Complex.I)
    have hzn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * r)
    have hzr : z.re ≤ 1 - d := by
      have hc := cos_gap hδ'₀ hδ'₁ (fun n => (min_le_left δ (1 / 4)).trans (hr n))
      change (Complex.exp ((↑(2 * Real.pi * r) : ℂ) * Complex.I)).re ≤
        1 - (1 - Real.cos (2 * Real.pi * δ'))
      rw [Complex.exp_ofReal_mul_I_re, sub_sub_cancel]
      exact hc
    let α := Complex.exp ((↑(-Real.pi / 4) : ℂ) * Complex.I)
    have hαn : ‖α‖ = 1 := Complex.norm_exp_ofReal_mul_I (-Real.pi / 4)
    have hαre : (2 / 3 : ℝ) ≤ α.re := by
      simp only [α, Complex.exp_ofReal_mul_I_re, neg_div, Real.cos_neg, Real.cos_pi_div_four]
      have hrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have hpow (k : ℕ) : (α * z ^ k).re = Real.cos (freq k * r - Real.pi / 4) := by
      dsimp [α, z]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      have he : (↑(-Real.pi / 4) : ℂ) * Complex.I +
            (k : ℂ) * ((↑(2 * Real.pi * r) : ℂ) * Complex.I) =
          (↑(freq k * r - Real.pi / 4) : ℂ) * Complex.I := by
        push_cast
        simp [freq]
        <;> ring
      rw [he, Complex.exp_ofReal_mul_I_re]
    have hval : evalNN P z = 1 + ∑ k ∈ F, (↑(c k) : ℂ) * z ^ k := by
      rw [evalNN, Polynomial.eval₂_eq_sum]
      change (∑ k ∈ P.support, (↑((P.coeff k : NNReal) : ℝ) : ℂ) * z ^ k) = _
      rw [← Finset.sum_erase_add _ _ hmem0]
      simp [F, c, hP₀, add_comm]
    have hidentify :
        (α * evalNN P z).re = α.re +
          ∑ k ∈ F, c k * Real.cos (freq k * r - Real.pi / 4) := by
      rw [hval, mul_add, mul_one, Complex.add_re, Finset.mul_sum, Complex.re_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      calc
        (α * ((↑(c k) : ℂ) * z ^ k)).re =
            ((↑(c k) : ℂ) * (α * z ^ k)).re := congrArg Complex.re (by ring)
        _ = _ := by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                        zero_mul, sub_zero, hpow]
    have ha := Complex.re_le_norm (α * evalNN P z)
    rw [norm_mul, hαn, one_mul, hidentify] at ha
    linarith only [ha, hαre, hP z hzn hzr]

theorem exists_radial_kernel (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℝ → ℝ) (B a R : ℝ), RadialKernel δ K B a R := by
  obtain ⟨E, hE, herror⟩ := circleCos_scaled_error
  obtain ⟨F, c, hF, hsign⟩ := sign_polynomial δ hδ
  let w (k : ℕ) : ℝ := c k * Real.sqrt (k : ℝ)
  have hw (k : ℕ) (hk : k ∈ F) : 0 ≤ w k :=
    mul_nonneg (hF k hk).2 (Real.sqrt_nonneg _)
  let K (r : ℝ) : ℝ := ∑ k ∈ F, w k * circleCos (freq k * r)
  let B : ℝ := ∑ k ∈ F, w k * (2 * Real.pi)
  have hB : 0 ≤ B :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (by positivity))
  let T : ℝ := (∑ k ∈ F, c k) * E
  have hT : 0 ≤ T := mul_nonneg (Finset.sum_nonneg (fun k hk => (hF k hk).2)) hE
  let R : ℝ := (2 * T + 1) ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨K, B, 1 / 2, R, hB, by norm_num, hR, ?_, ?_, ?_⟩
  · intro r
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (circleCos_le (freq k * r)) (hw k hk))
  · intro r hr havoid
    have hrpos : 0 < r := hR.trans_le hr
    have hsqrtpos : 0 < Real.sqrt r := Real.sqrt_pos.2 hrpos
    have hroot : 2 * T + 1 ≤ Real.sqrt r := Real.le_sqrt_of_sq_le hr
    have hsmall : T / Real.sqrt r ≤ 1 / 2 :=
      (div_le_iff₀ hsqrtpos).2 (by linarith)
    have hterm (k : ℕ) (hk : k ∈ F) :
        Real.sqrt r * (w k * circleCos (freq k * r)) ≤
          2 * (c k * Real.cos (freq k * r - Real.pi / 4)) +
            c k * (E / Real.sqrt r) := by
      calc
        _ = c k * (Real.sqrt (k : ℝ) * Real.sqrt r * circleCos (freq k * r)) := by
          dsimp [w]
          ring
        _ ≤ c k * (2 * Real.cos (freq k * r - Real.pi / 4) + E / Real.sqrt r) :=
          mul_le_mul_of_nonneg_left (herror k (hF k hk).1 r hrpos) (hF k hk).2
        _ = _ := by ring
    have hsum :
        Real.sqrt r * K r ≤
          2 * (∑ k ∈ F, c k * Real.cos (freq k * r - Real.pi / 4)) + T / Real.sqrt r := by
      calc
        _ = ∑ k ∈ F, Real.sqrt r * (w k * circleCos (freq k * r)) := by
          dsimp [K]
          rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ F, (2 * (c k * Real.cos (freq k * r - Real.pi / 4)) +
             c k * (E / Real.sqrt r)) := Finset.sum_le_sum hterm
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          dsimp [T]
          rw [mul_div_assoc]
    have hK : K r * Real.sqrt r ≤ -(1 / 2 : ℝ) := by
      rw [mul_comm]
      linarith [hsign r havoid]
    rw [← neg_div]
    exact (le_div_iff₀ hsqrtpos).2 hK
  · intro s
    have hcomm :
        (∑ p ∈ s, ∑ q ∈ s, K (dist q p)) =
          ∑ k ∈ F, w k * (∑ p ∈ s, ∑ q ∈ s, circleCos (freq k * dist q p)) := by
      dsimp [K]
      calc
        (∑ p ∈ s, ∑ q ∈ s, ∑ k ∈ F, w k * circleCos (freq k * dist q p)) =
            ∑ p ∈ s, ∑ k ∈ F, ∑ q ∈ s, w k * circleCos (freq k * dist q p) := by
          apply Finset.sum_congr rfl
          intro p _
          exact Finset.sum_comm
        _ = ∑ k ∈ F, ∑ p ∈ s, ∑ q ∈ s, w k * circleCos (freq k * dist q p) :=
          Finset.sum_comm
        _ = _ := by simp only [Finset.mul_sum]
    rw [hcomm]
    exact Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (circleCos_psd (freq k) s))

theorem erdos_465_complex (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (o : ℂ) (s : Finset ℂ),
      (∀ p ∈ s, dist p o ≤ X) → Good δ s → (s.card : ℝ) < C * Real.sqrt X := by
  obtain ⟨K, B, a, R, hK⟩ := exists_radial_kernel δ hδ
  exact bound_of_kernel hδ hK

theorem erdos_465 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (o : EuclideanSpace ℝ (Fin 2)) (s : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ s, dist p o ≤ X) →
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → AvoidsIntegers δ (dist p q)) →
      (s.card : ℝ) < C * Real.sqrt X := by
  classical
  obtain ⟨C, hC, h⟩ := erdos_465_complex δ hδ
  refine ⟨C, hC, ?_⟩
  intro X hX o s hball hs
  let f := Complex.orthonormalBasisOneI.repr.symm
  have hi : Isometry f := f.isometry
  have hball' (p : ℂ) (hp : p ∈ s.image f) : dist p (f o) ≤ X := by
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    rw [hi.dist_eq]
    exact hball p' hp'
  have hs' : Good δ (s.image f) := by
    intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    rw [hi.dist_eq]
    exact hs p' hp' q' hq' (fun heq => hpq (congrArg f heq))
  simpa only [Finset.card_image_of_injective s hi.injective] using
    h X hX (f o) (s.image f) hball' hs'

end JSP000377

#print axioms JSP000377.erdos_465
