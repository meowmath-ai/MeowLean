import JSP000930TraceExpressionEnvironment

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem traceEnv_cutOn (p : PolyTrace B J) (site : J → ComplexBits B) (z : J)
    (y : ComplexBits B) {m : B}
    (hp : m ≤ coeffValue p.coeff)
    (hsite : ∀ j,(site j).CutOn m) (hy : y.CutOn m) :
    ∀ a, (traceEnv p site z y a).CutOn m := by
  have hCoeff := (le_coeffValue_iff m p.coeff).mp hp
  intro a
  rcases a with i | a
  · exact hCoeff _ (List.getElem_mem i.2)
  rcases a with i | a
  · exact hsite i.1
  rcases a with b | g
  · cases b
    · exact hsite z
    · exact hy
  · exact ComplexBits.checked_cutOn _ m

theorem gridPoint_norm_le {R : ℕ} (g : RatGrid R) : ‖gridPoint g‖ ≤ (R : ℝ) := by
  have h : ((g.1.1 : ℝ)^2 + (g.1.2 : ℝ)^2) ≤ (R : ℝ)^2 := by exact_mod_cast g.2
  have hSq : ‖gridPoint g‖^2 ≤ (R : ℝ)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    change (g.1.1 : ℝ) * (g.1.1 : ℝ) + (g.1.2 : ℝ) * (g.1.2 : ℝ) ≤ (R : ℝ)^2
    simpa only [pow_two] using h
  by_contra hn
  have hh := lt_of_not_ge hn
  have hR : 0 ≤ (R : ℝ) := by positivity
  nlinarith [mul_pos (sub_pos.mpr hh)
    (add_pos_of_pos_of_nonneg (hR.trans_lt hh) hR)]

open scoped Classical in
theorem exists_refining_polynomial_pin (site : J → ComplexBits B)
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
  refine ⟨q,rfl,rfl,rfl,?_⟩
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

end JSP000930.Negative
