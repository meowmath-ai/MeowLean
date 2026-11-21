import JSP000930PositiveReciprocalCut

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem trace_reciprocalCut {p : ℕ → B} {m : B} (hpm : ∀ n, p n ≤ m)
    {u : RatPresentation → B} {x : ℝ} (hu : ProperCutOn m u)
    (h : CutDecisionTrace p u x) (hx : 0 < x) :
    CutDecisionTrace p (reciprocalCutBits u) (1 / x) := by
  constructor
  · intro q hq
    have hq' : (q.value : ℝ) * x < 1 := (lt_div_iff₀ hx).mp hq
    have hR : ∃ t : ℚ, x < (t : ℝ) ∧ 0 < t ∧ q.value * t < 1 := by
      by_cases hqpos : (0 : ℝ) < (q.value : ℝ)
      · have ht : x < 1 / (q.value : ℝ) := (lt_div_iff₀ hqpos).mpr (by
          simpa only [mul_comm] using hq')
        obtain ⟨t,hxt,htt⟩ := exists_rat_btwn ht
        have hT₀ : (0 : ℝ) < (t : ℝ) := hx.trans hxt
        have hT₁ : (q.value : ℝ) * (t : ℝ) < 1 := by
          simpa only [mul_comm] using (lt_div_iff₀ hqpos).mp htt
        exact ⟨t,hxt,by exact_mod_cast hT₀, by exact_mod_cast hT₁⟩
      · obtain ⟨t,hxt,_⟩ := exists_rat_btwn (show x < x + 1 by linarith)
        have hT₀ : (0 : ℝ) < (t : ℝ) := hx.trans hxt
        have hT₁ : (q.value : ℝ) * (t : ℝ) < 1 :=
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hqpos) hT₀.le).trans_lt zero_lt_one
        exact ⟨t,hxt,by exact_mod_cast hT₀, by exact_mod_cast hT₁⟩
    obtain ⟨t,hxt,htt,hqt⟩ := hR
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective t
    have hxr : x < (r.value : ℝ) := by rwa [hr]
    have hr' : 0 < r.value ∧ q.value * r.value < 1 := by rw [hr]; exact ⟨htt,hqt⟩
    obtain ⟨n,hn⟩ := h.above r hxr
    exact ⟨n, hn.trans (le_iSup_of_le r (le_iSup (fun _ : 0 < r.value ∧ q.value * r.value < 1 => (u r)ᶜ) hr'))⟩
  · intro q hq
    have hqpos : (0 : ℝ) < (q.value : ℝ) := (one_div_pos.mpr hx).trans hq
    have hlt : 1 / (q.value : ℝ) < x := (div_lt_iff₀ hqpos).mpr (by
      simpa only [mul_comm] using (div_lt_iff₀ hx).mp hq)
    obtain ⟨t,hT,htX⟩ := exists_rat_btwn hlt
    obtain ⟨a,ha⟩ := ratPresentation_value_surjective t
    have hAX : (a.value : ℝ) < x := by rwa [ha]
    have hAT : 1 / (q.value : ℝ) < (a.value : ℝ) := by rwa [ha]
    obtain ⟨n,hn⟩ := h.below a hAX
    refine ⟨n,?_⟩
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iSup_iff.mpr
    intro r
    apply disjoint_iSup_iff.mpr
    intro hr
    have hR₁ : (r.value : ℝ) * (q.value : ℝ) < 1 := by
      have H : (q.value : ℝ) * (r.value : ℝ) < 1 := by exact_mod_cast hr.2
      simpa only [mul_comm] using H
    have hR₂ : (r.value : ℝ) < 1 / (q.value : ℝ) := (lt_div_iff₀ hqpos).mpr hR₁
    have hRa : r.value ≤ a.value := by exact_mod_cast (hR₂.trans hAT).le
    have hn' : p n ≤ u r := (le_inf (hpm n) hn).trans (hu.2.2.1 r a hRa)
    exact disjoint_compl_right.mono_left hn'

end JSP000930.BooleanAnalysis
