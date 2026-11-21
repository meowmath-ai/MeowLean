import JSP000930ReciprocalCutTrace

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem cut_order_fail_survives {m : B} {u v : RatPresentation → B}
    (hu : ProperCutOn m u)
    (h : ¬ m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v) :
    ∃ s : B, s ≠ ⊥ ∧ s ≤ m ∧
      ∀ {p : ℕ → B}, Antitone p → (∀ n,p n ≠ ⊥) → (∀ n,p n ≤ s) →
      ∀ {x y : ℝ}, CutDecisionTrace p u x → CutDecisionTrace p v y → y < x := by
  obtain ⟨q,r,s,hnz,hsm,hqr,hur,hvq⟩ := nonzero_cut_order_countercell hu h
  refine ⟨s,hnz,hsm,?_⟩
  intro p hp hn hps x y htx hty
  have hLeft := trace_forcedMember_le hp hn htx r ⟨0,(hps 0).trans hur⟩
  have hRight := trace_forcedAbsent_ge hp hn hty q ⟨0,(hps 0).trans hvq⟩
  have hStrict : (q.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hqr
  exact (hRight.trans_lt hStrict).trans_le hLeft

theorem cut_eq_fail_survives {m : B} {u v : RatPresentation → B}
    (hu : ProperCutOn m u) (hv : ProperCutOn m v)
    (h : ¬ m ≤ weightedRationalSet u =ᴮ weightedRationalSet v) :
    ∃ s : B, s ≠ ⊥ ∧ s ≤ m ∧
      ∀ {p : ℕ → B}, Antitone p → (∀ n,p n ≠ ⊥) → (∀ n,p n ≤ s) →
      ∀ {x y : ℝ}, CutDecisionTrace p u x → CutDecisionTrace p v y → x ≠ y := by
  rw [bSet.eq_iff_subset_subset, le_inf_iff] at h
  by_cases h₁ : m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v
  · have h₂ : ¬ m ≤ weightedRationalSet v ⊆ᴮ weightedRationalSet u :=
      fun hd => h ⟨h₁,hd⟩
    obtain ⟨s,hs,hm,hSep⟩ := cut_order_fail_survives hv h₂
    exact ⟨s,hs,hm,fun {_} hp hn hps {_ _} hu hv => (hSep hp hn hps hv hu).ne⟩
  · obtain ⟨s,hs,hm,hSep⟩ := cut_order_fail_survives hu h₁
    exact ⟨s,hs,hm,fun {_} hp hn hps {_ _} hu hv => (hSep hp hn hps hu hv).ne.symm⟩

theorem complex_eq_fail_survives {m : B} {u v : ComplexBits B}
    (hu : u.CutOn m) (hv : v.CutOn m) (h : ¬ m ≤ u.name =ᴮ v.name) :
    ∃ s : B, s ≠ ⊥ ∧ s ≤ m ∧
      ∀ {p : ℕ → B}, Antitone p → (∀ n,p n ≠ ⊥) → (∀ n,p n ≤ s) →
      ∀ {x y : ℂ}, ComplexDecisionTrace p u x → ComplexDecisionTrace p v y → x ≠ y := by
  rw [ComplexBits.name_eq, le_inf_iff] at h
  by_cases h₁ : m ≤ weightedRationalSet u.re =ᴮ weightedRationalSet v.re
  · have h₂ : ¬ m ≤ weightedRationalSet u.im =ᴮ weightedRationalSet v.im :=
      fun hd => h ⟨h₁,hd⟩
    obtain ⟨s,hs,hm,hSep⟩ := cut_eq_fail_survives hu.2 hv.2 h₂
    refine ⟨s,hs,hm,fun {_} hp hn hps {_ _} hx hy he => ?_⟩
    exact hSep hp hn hps hx.2 hy.2 (congrArg Complex.im he)
  · obtain ⟨s,hs,hm,hSep⟩ := cut_eq_fail_survives hu.1 hv.1 h₁
    refine ⟨s,hs,hm,fun {_} hp hn hps {_ _} hx hy he => ?_⟩
    exact hSep hp hn hps hx.1 hy.1 (congrArg Complex.re he)

end JSP000930.BooleanAnalysis
