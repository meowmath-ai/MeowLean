import JSP000930AnalyticWeightedRational
import Mathlib

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

theorem ratPresentation_value_surjective : Function.Surjective RatPresentation.value := by
  intro q
  refine ⟨⟨q.num.toNat, (-q.num).toNat, q.den, q.den_pos⟩, ?_⟩
  have h : ((q.num.toNat : ℕ) : ℤ) - (((-q.num).toNat : ℕ) : ℤ) = q.num := by omega
  have hr : ((q.num.toNat : ℕ) : ℚ) - (((-q.num).toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    exact_mod_cast h
  change ((q.num.toNat : ℚ) - ((-q.num).toNat : ℚ)) / (q.den : ℚ) = q
  rw [hr, Rat.num_div_den]

theorem ratPresentation_cross_le (q r : RatPresentation) :
    q.value ≤ r.value ↔ q.pos*r.den + r.neg*q.den ≤ r.pos*q.den + q.neg*r.den := by
  have hq : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hr : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  unfold RatPresentation.value
  rw [div_le_div_iff₀ hq hr, sub_mul, sub_mul]
  constructor
  · intro h
    have h' : (q.pos : ℚ)*r.den + (r.neg : ℚ)*q.den ≤
        (r.pos : ℚ)*q.den + (q.neg : ℚ)*r.den := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (q.pos : ℚ)*r.den + (r.neg : ℚ)*q.den ≤
        (r.pos : ℚ)*q.den + (q.neg : ℚ)*r.den := by exact_mod_cast h
    linarith

theorem ratPresentation_value_dense {q r : RatPresentation} (h : q.value < r.value) :
    ∃ s : RatPresentation, q.value < s.value ∧ s.value < r.value := by
  obtain ⟨s,hs⟩ := ratPresentation_value_surjective ((q.value+r.value)/2)
  refine ⟨s, ?_⟩
  rw [hs]
  constructor <;> linarith

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def roundedLiminfBits (u : ℕ → RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), ⨆ N : ℕ,
    ⨅ n : {n : ℕ // N ≤ n}, u n.val r

theorem roundedLiminfBits_downward (u : ℕ → RatPresentation → B) {q r : RatPresentation}
    (hqr : q.value ≤ r.value) :
    roundedLiminfBits u r ≤ roundedLiminfBits u q := by
  unfold roundedLiminfBits
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  exact (le_iSup (fun _ : q.value < s.value => ⨆ N : ℕ,
    ⨅ n : {n : ℕ // N ≤ n}, u n.val s) (hqr.trans_lt hs)).trans
      (le_iSup (fun t : RatPresentation => ⨆ (_ : q.value < t.value), ⨆ N : ℕ,
        ⨅ n : {n : ℕ // N ≤ n}, u n.val t) s)

theorem roundedLiminfBits_respects_presentation (u : ℕ → RatPresentation → B)
    (q r : RatPresentation) (h : q.value = r.value) :
    roundedLiminfBits u q = roundedLiminfBits u r :=
  le_antisymm (roundedLiminfBits_downward u h.ge) (roundedLiminfBits_downward u h.le)

theorem roundedLiminfBits_rounded (u : ℕ → RatPresentation → B) (q : RatPresentation) :
    roundedLiminfBits u q =
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), roundedLiminfBits u r := by
  apply le_antisymm
  · unfold roundedLiminfBits
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    obtain ⟨r,hqr,hrs⟩ := ratPresentation_value_dense hs
    apply le_trans _ (le_iSup_of_le r (le_iSup _ hqr))
    refine le_iSup_of_le s ?_
    exact le_iSup (fun _ : r.value < s.value => ⨆ N : ℕ,
      ⨅ n : {n : ℕ // N ≤ n}, u n.val s) hrs
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    exact roundedLiminfBits_downward u hr.le

noncomputable def roundedLiminfName (u : ℕ → RatPresentation → B) : bSet B :=
  weightedRationalSet (roundedLiminfBits u)

theorem roundedLiminfName_mem (u : ℕ → RatPresentation → B) (q : RatPresentation) :
    (ratName q ∈ᴮ roundedLiminfName u) = roundedLiminfBits u q :=
  ratName_mem_weightedRationalSet _ q

theorem roundedLiminfBits_nonempty_below (u : ℕ → RatPresentation → B) (p : B)
    (r : RatPresentation) (N : ℕ) (hr : ∀ n : ℕ, N ≤ n → p ≤ u n r) :
    p ≤ ⨆ q : RatPresentation, roundedLiminfBits u q := by
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (r.value-1)
  have hlt : q.value < r.value := by rw [hq]; linarith
  apply le_trans _ (le_iSup _ q)
  unfold roundedLiminfBits
  apply le_trans _ (le_iSup _ r)
  apply le_trans _ (le_iSup _ hlt)
  apply le_trans _ (le_iSup _ N)
  exact le_iInf (fun n => hr n.val n.property)

theorem roundedLiminfBits_proper_below (u : ℕ → RatPresentation → B) (p : B)
    (r : RatPresentation) (N : ℕ)
    (hr : ∀ (s : RatPresentation), r.value < s.value → ∀ n : ℕ, N ≤ n → p ≤ (u n s)ᶜ) :
    p ≤ (roundedLiminfBits u r)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le, roundedLiminfBits, inf_iSup_eq]
  apply iSup_le
  intro s
  rw [inf_iSup_eq]
  apply iSup_le
  intro hs
  rw [inf_iSup_eq]
  apply iSup_le
  intro M
  let n : {n : ℕ // M ≤ n} := ⟨max N M, le_max_right N M⟩
  have h₁ := hr s hs (max N M) (le_max_left N M)
  calc
    p ⊓ (⨅ j : {n : ℕ // M ≤ n}, u j.val s) ≤ (u n.val s)ᶜ ⊓ u n.val s :=
      inf_le_inf h₁ (iInf_le _ n)
    _ ≤ ⊥ := by simp

end JSP000930.BooleanAnalysis
