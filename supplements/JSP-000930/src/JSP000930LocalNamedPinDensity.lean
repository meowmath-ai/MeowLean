import JSP000930MarkedOnePinRefinement

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.CantorCodes

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def DensePalette (H : ℕ → ComplexBits B) : Prop :=
  ∀ (x : ComplexBits B) (m : B), x.CutOn m → ∀ e : ℚ, 0 < e →
    m ≤ ⨆ n : ℕ, distanceLe x (H n) e

theorem cutOn_mono930 {m r : B} {x : ComplexBits B} (h : x.CutOn m) (hr : r ≤ m) :
    x.CutOn r := ⟨properCutOn_mono hr h.1,properCutOn_mono hr h.2⟩

open scoped Classical in
theorem exists_refining_trace_with_pin (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) (m : B)
    (hm : m ≠ ⊥) (hP : m ≤ polyValid site H p)
    (z : J) (hz : z ∉ p.pins)
    (hSite : ∀ i,(site i).CutOn m) (hY : ∀ n,(H z n).CutOn m)
    (hSep : ∀ i ∈ p.pins, m ≤ ((site z).name =ᴮ (site i).name)ᶜ)
    (hDense : DensePalette (H z)) :
    ∃ (s : B) (q : PolyTrace B J), s ≠ ⊥ ∧ s ≤ m ∧ z ∈ q.pins ∧
      s ≤ (polynomialQ site H).refines (some q) (some p) := by
  let O : ComplexBits B := ComplexBits.checked 0
  let u := traceEnv p site z O
  let a := oldSiteAtoms p
  let iz := newSiteAtom p
  let D := traceDenominator p
  haveI : Countable (TraceAtoms p) := inferInstance
  haveI : Nonempty (TraceAtoms p) := ⟨iz⟩
  have hu : ∀ i,(u i).CutOn m :=
    traceEnv_cutOn p site z O (hP.trans inf_le_left) hSite (ComplexBits.checked_cutOn 0 m)
  have hApart : ∀ i ∈ a, m ≤ ((u iz).name =ᴮ (u i).name)ᶜ := by
    intro i hi
    obtain ⟨j,rfl⟩ := oldSiteAtoms_mem p hi
    exact hSep j.1 j.2
  have hD : m ≤ positiveCutValue (D.eval u).normSq :=
    named_vanishing_positive u iz a m hu hApart
  obtain ⟨k,L,hk,hkm,hL,hOld⟩ := exists_finite_normBound u a m hm hu
  obtain ⟨d,t,ht,htk,htD⟩ := exists_nonzero_below_choice_r135 k hk
    (fun d : {d : RatPresentation // 0 < d.value} => (D.eval u).normSq d.1) (hkm.trans hD)
  let r : ℚ := min 1 d.1.value / 2
  have hr0 : 0 < min (1 : ℚ) d.1.value := lt_min zero_lt_one d.2
  have hr : 0 < r := div_pos hr0 (by norm_num)
  have hr' : r ≤ min 1 d.1.value := by
    dsimp [r]
    linarith
  have hrSq : r^2 ≤ d.1.value :=
    (show r^2 ≤ r by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_left (hr'.trans (min_le_left _ _)) hr.le).trans_eq (mul_one r)
      ).trans (hr'.trans (min_le_right _ _))
  let b : ℚ := p.budget / 2
  have hb : 0 < b := div_pos p.budget_pos (by norm_num)
  have hbP : b ≤ p.budget := by dsimp [b]; linarith [p.budget_pos]
  have hbP' : 0 < p.budget - b := by dsimp [b]; linarith [p.budget_pos]
  let M : ℚ := ((p.radius : ℚ) + L)^a.length
  have hM : 0 ≤ M := pow_nonneg (add_nonneg (by positivity) hL) _
  let η := ((p.budget - b) * r) / (M + 1)
  have hM' : 0 < M + 1 := by linarith
  have hη : 0 < η := div_pos (mul_pos hbP' hr) hM'
  have hQuant : η * M ≤ (p.budget - b) * r := by
    calc
      η * M ≤ η * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hM')
  have htM := htk.trans hkm
  have hCentre : (p.eval (site z)).CutOn t :=
    cutOn_mono930 (eval_cutOn_of_coeff (hP.trans inf_le_left) (hSite z)) htM
  obtain ⟨n,s,hs,hst,hS⟩ := exists_nonzero_below_choice_r135 t ht
    (fun n => distanceLe (p.eval (site z)) (H z n) η) (hDense _ t hCentre η hη)
  have hsM := hst.trans htM
  have hY' := cutOn_mono930 (hY n) hsM
  have hNear : s ≤ distanceLe (H z n) (p.eval (site z)) η :=
    distanceLe_symm_mono (cutOn_mono930 hCentre hst) hY' hη.le le_rfl hS
  have hDen : s ≤ ((traceDenominator p).eval (traceEnv p site z (H z n))).normSq d.1 := by
    rw [traceEnv_denominator_target_irrelevant p site z (H z n) O]
    exact hst.trans htD
  obtain ⟨q,hq,_,_,hRef⟩ := exists_refining_polynomial_pin site H p s z n hz
    (hsM.trans hP) (fun i => cutOn_mono930 (hSite i) hsM) hY'
    (fun i hi => hsM.trans (hSep i hi)) L η r b hL hη.le hr hb hbP hQuant
    (fun i hi => (hst.trans htk).trans (hOld (siteAtom p ⟨i,hi⟩)
      (mem_oldSiteAtoms p ⟨i,hi⟩))) hNear d.1 hrSq hDen
  refine ⟨s,q,hs,hsM,?_,hRef⟩
  rw [hq]
  exact Finset.mem_insert_self _ _

end JSP000930.Negative
