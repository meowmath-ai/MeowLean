import JSP000930LocalNamedPinDensity

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative
open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing JSP000933.CantorCodes
variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def AvoidingPalette (H : ℕ → ComplexBits B) : Prop :=
  ∀ (x y : ComplexBits B) (m : B), x.CutOn m → y.CutOn m → ∀ e : ℚ, 0 < e →
    m ≤ ⨆ n : ℕ, distanceLe x (H n) e ⊓ ((H n).name =ᴮ y.name)ᶜ

open scoped Classical in
theorem exists_refining_polynomial_pin_with_value (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) (m : B)
    (z : J) (n : ℕ) (hz : z ∉ p.pins)
    (hP : m ≤ polyValid site H p)
    (hSite : ∀ i,(site i).CutOn m) (hY : (H z n).CutOn m)
    (hSep : ∀ i ∈ p.pins, m ≤ ((site z).name =ᴮ (site i).name)ᶜ)
    (L η r b : ℚ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hr : 0 < r)
    (hb : 0 < b) (hbP : b ≤ p.budget)
    (hQ : η * ((p.radius : ℚ) + L)^(oldSiteAtoms p).length ≤ (p.budget - b) * r)
    (hOld : ∀ i ∈ p.pins, m ≤ distanceLe (site i) (ComplexBits.checked (0 : ℂ)) L)
    (hNear : m ≤ distanceLe (H z n) (p.eval (site z)) η)
    (d : RatPresentation) (hd : r^2 ≤ d.value)
    (hD : m ≤ ((traceDenominator p).eval (traceEnv p site z (H z n))).normSq d) :
    ∃ q : PolyTrace B J, q.pins = insert z p.pins ∧ q.radius = p.radius ∧ q.budget = b ∧
      (m ≤ (q.eval (site z)).name =ᴮ (H z n).name) ∧
      m ≤ (polynomialQ site H).refines (some q) (some p) := by
  let u := traceEnv p site z (H z n)
  let A := coefficientAtoms p
  let t := oldSiteAtoms p
  let iz := newSiteAtom p
  let iy := newValueAtom p
  haveI : Countable (TraceAtoms p) := inferInstance
  haveI : Nonempty (TraceAtoms p) := ⟨iz⟩
  have hu : ∀ i,(u i).CutOn m :=
    traceEnv_cutOn p site z (H z n) (hP.trans inf_le_left) hSite hY
  have hA : ExprPoly.CoeffSafe u m A := by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    intro g hg
    exact (List.not_mem_nil hg).elim
  have ht : ∀ i ∈ t, m ≤ ((u iz).name =ᴮ (u i).name)ᶜ := by
    intro i hi
    obtain ⟨k,rfl⟩ := oldSiteAtoms_mem p hi
    exact hSep k.1 k.2
  have hEnv : A.map (Expr.eval u) = p.coeff := coefficientAtoms_eval p site z (H z n)
  obtain ⟨P,hPexpr,hPA,hPz,hPold⟩ := ExprPoly.named_one_pin_exact u m A t iz iy hu hA ht
  let q : PolyTrace B J := ⟨P, insert z p.pins, p.radius, b, hb⟩
  have hEq (i : J) (hi : i ∈ p.pins) : m ≤ (q.eval (site i)).name =ᴮ (p.eval (site i)).name := by
    have h := hPold (siteAtom p ⟨i,hi⟩) (mem_oldSiteAtoms p ⟨i,hi⟩)
    rw [hEnv] at h
    exact h
  have hValid : m ≤ polyValid site H q := by
    unfold polyValid
    refine le_inf ((le_coeffValue_iff m P).mpr hPA) ?_
    unfold paletteValue
    apply le_iInf
    intro k
    have hk : k.1 ∈ insert z p.pins := k.2
    rcases Finset.mem_insert.mp hk with hzz | hOldPin
    · have ht₀ : m ≤ (q.eval (site z)).name =ᴮ (H z n).name := hPz
      exact le_iSup_of_le n (hzz.symm ▸ ht₀)
    · have hOldVal : m ≤ ⨆ ℓ : ℕ, (p.eval (site k.1)).name =ᴮ (H k.1 ℓ).name :=
        (hP.trans inf_le_right).trans (iInf_le
          (fun i : {j : J // j ∈ p.pins} => ⨆ ℓ : ℕ,
            (p.eval (site i.val)).name =ᴮ (H i.val ℓ).name) ⟨k.val,hOldPin⟩)
      apply (le_inf (hEq k.1 hOldPin) hOldVal).trans
      rw [inf_iSup_eq]
      apply iSup_le
      intro ℓ
      exact le_iSup_of_le ℓ (bSet.bv_trans inf_le_left inf_le_right)
  refine ⟨q,rfl,rfl,rfl,hPz,?_⟩
  change m ≤ (polyValid site H q ⊓ polyValid site H p) ⊓ refinesValue site q p
  refine le_inf (le_inf hValid hP) ?_
  unfold refinesValue
  refine le_inf ?_ (le_inf ?_ ?_)
  · have h : p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧ p.radius ≤ q.radius :=
      ⟨fun _ hh => Finset.mem_insert_of_mem hh,hbP,le_rfl⟩
    simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left h,le_top]
  · unfold agreementValue
    exact le_iInf fun i => hEq i.1 i.2
  · unfold discValue
    apply le_iInf
    intro g
    have hh : ∀ i ∈ t, m ≤ distanceLe (u i) (ComplexBits.checked (0 : ℂ)) L := by
      intro i hi
      obtain ⟨j,rfl⟩ := oldSiteAtoms_mem p hi
      exact hOld j.1 j.2
    have hw : m ≤ distanceLe (u (gridAtom p g)) (ComplexBits.checked (0 : ℂ)) (p.radius : ℚ) := by
      apply checked_distanceLe
      simpa only [dist_zero_right, Rat.cast_natCast] using gridPoint_norm_le g
    have hN : m ≤ distanceLe (u iy) ((ExprPoly.atExpr A (.atom iz)).eval u) η := by
      rw [ExprPoly.atExpr_eval,hEnv]
      exact hNear
    have Hq := ExprPoly.named_displacement_disc_control u m A t iz iy (gridAtom p g)
      p.radius L η (p.budget - b) r (by positivity) hL hη hr hQ hu hA hh hw hN d hd hD
    rw [← hPexpr,hEnv] at Hq
    exact Hq

open scoped Classical in
theorem exists_refining_trace_with_pin_avoiding (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) (m : B)
    (hm : m ≠ ⊥) (hP : m ≤ polyValid site H p)
    (z : J) (hz : z ∉ p.pins)
    (hSite : ∀ i,(site i).CutOn m) (hY : ∀ n,(H z n).CutOn m)
    (hSep : ∀ i ∈ p.pins, m ≤ ((site z).name =ᴮ (site i).name)ᶜ)
    (y : ComplexBits B) (hy : y.CutOn m) (hDense : AvoidingPalette (H z)) :
    ∃ (s : B) (q : PolyTrace B J), s ≠ ⊥ ∧ s ≤ m ∧ z ∈ q.pins ∧
      s ≤ (polynomialQ site H).refines (some q) (some p) ∧
      s ≤ ((q.eval (site z)).name =ᴮ y.name)ᶜ := by
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
    (fun n => distanceLe (p.eval (site z)) (H z n) η ⊓ ((H z n).name =ᴮ y.name)ᶜ)
    (hDense _ y t hCentre (cutOn_mono930 hy htM) η hη)
  have hsM := hst.trans htM
  have hY' := cutOn_mono930 (hY n) hsM
  have hNear : s ≤ distanceLe (H z n) (p.eval (site z)) η :=
    distanceLe_symm_mono (cutOn_mono930 hCentre hst) hY' hη.le le_rfl (hS.trans inf_le_left)
  have hDen : s ≤ ((traceDenominator p).eval (traceEnv p site z (H z n))).normSq d.1 := by
    rw [traceEnv_denominator_target_irrelevant p site z (H z n) O]
    exact hst.trans htD
  obtain ⟨q,hq,_,_,hEq,hRef⟩ := exists_refining_polynomial_pin_with_value site H p s z n hz
    (hsM.trans hP) (fun i => cutOn_mono930 (hSite i) hsM) hY'
    (fun i hi => hsM.trans (hSep i hi)) L η r b hL hη.le hr hb hbP hQuant
    (fun i hi => (hst.trans htk).trans (hOld (siteAtom p ⟨i,hi⟩)
      (mem_oldSiteAtoms p ⟨i,hi⟩))) hNear d.1 hrSq hDen
  refine ⟨s,q,hs,hsM,?_,hRef,?_⟩
  · rw [hq]
    exact Finset.mem_insert_self _ _
  · apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff_inf_le]
    have hb1 : s ⊓ ((q.eval (site z)).name =ᴮ y.name) ≤ (H z n).name =ᴮ y.name :=
      bSet.bv_trans ((inf_le_left.trans hEq).trans_eq bSet.bv_eq_symm) inf_le_right
    exact (le_inf hb1 (inf_le_left.trans (hS.trans inf_le_right))).trans_eq (inf_compl_self _)

end JSP000930.Negative
