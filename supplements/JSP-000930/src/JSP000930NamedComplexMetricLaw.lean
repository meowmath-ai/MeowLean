import JSP000930PolynomialTraceValues
import JSP000930AnalyticDecisionCompletion
import Mathlib.Tactic

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_complex_decision_completion {J : Type} [Countable J] [Nonempty J]
    (u : J → ComplexBits B) (m : B) (hm : m ≠ ⊥) (hu : ∀ j, (u j).CutOn m) :
    ∃ (p : ℕ → B) (w : J → ℂ), Antitone p ∧ (∀ n, p n ≠ ⊥) ∧
      (∀ n, p n ≤ m) ∧ ∀ j, ComplexDecisionTrace p (u j) (w j) := by
  let β : J × Bool → RatPresentation → B := fun j => if j.2 then (u j.1).im else (u j.1).re
  have hβ : ∀ j, ProperCutOn m (β j) := by
    rintro ⟨j,b⟩
    cases b
    · exact (hu j).1
    · exact (hu j).2
  let V : ℕ → Unit → B := fun _ _ => ⊤
  have hV : ∀ n, m ≤ ⨆ x, V n x := fun n =>
    le_iSup_of_le () le_top
  obtain ⟨p,_,z,hp,hnz,hpm,_,ht⟩ := mixed_cut_decision_completion β m hm hβ V hV
  exact ⟨p, (fun j => ⟨z (j,false),z (j,true)⟩), hp, hnz, hpm,
    fun j => ⟨ht (j,false), ht (j,true)⟩⟩

theorem proper_distanceCut {m : B} {x y : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) : ProperCutOn m (distanceCut x y) :=
  ComplexBits.normSq_cutOn (ComplexBits.add_cutOn hx (ComplexBits.neg_cutOn hy))

theorem trace_distanceCut {p : ℕ → B} (hp : Antitone p) {m : B}
    (hpm : ∀ n, p n ≤ m) {x y : ComplexBits B} {a b : ℂ}
    (hx : x.CutOn m) (hy : y.CutOn m)
    (hta : ComplexDecisionTrace p x a) (htb : ComplexDecisionTrace p y b) :
    CutDecisionTrace p (distanceCut x y) ((dist a b) ^ 2) := by
  have ht := hta.add hp hpm (htb.neg hpm hy) hx (ComplexBits.neg_cutOn hy)
  have ht' := ht.normSq hp hpm (ComplexBits.add_cutOn hx (ComplexBits.neg_cutOn hy))
  simpa only [distanceCut, dist_eq_norm, sub_eq_add_neg, Complex.normSq_eq_norm_sq] using ht'

theorem trace_distanceLe {p : ℕ → B} (hp : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m) {x y : ComplexBits B} {a b : ℂ}
    (hx : x.CutOn m) (hy : y.CutOn m) (ha : ComplexDecisionTrace p x a)
    (hb : ComplexDecisionTrace p y b) {e : ℚ} (he : 0 ≤ e)
    (h : m ≤ distanceLe x y e) : dist a b ≤ (e : ℝ) := by
  have hsq := trace_subset_le hp hnz hpm
    (trace_distanceCut hp hpm hx hy ha hb)
    (checkedRealBits_traces p ((e : ℝ)^2)) h
  have he' : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  by_contra h'
  have hlt := lt_of_not_ge h'
  have hn := add_pos_of_pos_of_nonneg (he'.trans_lt hlt) he'
  nlinarith [mul_pos (sub_pos.mpr hlt) hn]

theorem distanceLe_of_finite_metric_law {J : Type} [Countable J] [Nonempty J]
    (u : J → ComplexBits B) (m : B) (hu : ∀ j, (u j).CutOn m)
    (i j : J) (e : ℚ)
    (hLaw : ∀ (p : ℕ → B) (w : J → ℂ), Antitone p → (∀ n, p n ≠ ⊥) →
      (∀ n, p n ≤ m) → (∀ k, ComplexDecisionTrace p (u k) (w k)) →
      (dist (w i) (w j)) ^ 2 ≤ (e : ℝ) ^ 2) :
    m ≤ distanceLe (u i) (u j) e := by
  by_contra h
  obtain ⟨q,r,s,hs,hsM,hqr,hL,hR⟩ :=
    nonzero_cut_order_countercell (proper_distanceCut (hu i) (hu j)) h
  have huS : ∀ k, (u k).CutOn s := fun k =>
    ⟨properCutOn_mono hsM (hu k).1, properCutOn_mono hsM (hu k).2⟩
  obtain ⟨p,w,hp,hnz,hps,ht⟩ := exists_complex_decision_completion u s hs huS
  have hpm : ∀ n, p n ≤ m := fun n => (hps n).trans hsM
  have hl := trace_forcedMember_le hp hnz (trace_distanceCut hp hpm (hu i) (hu j) (ht i) (ht j))
    r ⟨0,(hps 0).trans hL⟩
  have hr := trace_forcedAbsent_ge hp hnz (checkedRealBits_traces p ((e : ℝ)^2))
    q ⟨0,(hps 0).trans hR⟩
  have hqr' : (q.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hqr
  exact (not_le_of_gt ((hr.trans_lt hqr').trans_le hl)) (hLaw p w hp hnz hpm ht)

theorem distanceLe_self {m : B} {x : ComplexBits B} (hx : x.CutOn m) (e : ℚ) :
    m ≤ distanceLe x x e := by
  refine distanceLe_of_finite_metric_law (fun _ : Unit => x) m (fun _ => hx) () () e ?_
  intro p w hp hnz hpm ht
  simpa only [dist_self, zero_pow (by decide : 2 ≠ 0)] using (sq_nonneg (e : ℝ))

theorem distanceLe_triangle {m : B} {x y z : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) (hz : z.CutOn m)
    {e f : ℚ} (he : 0 ≤ e) (hf : 0 ≤ f)
    (hxy : m ≤ distanceLe x y e) (hyz : m ≤ distanceLe y z f) :
    m ≤ distanceLe x z (e + f) := by
  let u : Fin 3 → ComplexBits B := ![x,y,z]
  have hu : ∀ i, (u i).CutOn m := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  refine distanceLe_of_finite_metric_law u m hu 0 2 (e + f) ?_
  intro p w hp hnz hpm ht
  have h₀ : ComplexDecisionTrace p x (w 0) := ht 0
  have h₁ : ComplexDecisionTrace p y (w 1) := ht 1
  have h₂ : ComplexDecisionTrace p z (w 2) := ht 2
  have hE := trace_distanceLe hp hnz hpm hx hy h₀ h₁ he hxy
  have hF := trace_distanceLe hp hnz hpm hy hz h₁ h₂ hf hyz
  have hT : dist (w 0) (w 2) ≤ ((e + f : ℚ) : ℝ) := by
    rw [Rat.cast_add]
    exact (dist_triangle (w 0) (w 1) (w 2)).trans (add_le_add hE hF)
  exact pow_le_pow_left₀ dist_nonneg hT 2

end JSP000930.Negative
