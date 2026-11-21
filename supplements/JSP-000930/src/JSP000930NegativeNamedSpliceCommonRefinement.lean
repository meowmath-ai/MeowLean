import JSP000930NegativeSpliceAtomicValue
import JSP000930NegativeNamedSpliceGuard

open Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def eraseSplicePin (p : PolyTrace B J) (z : J) : PolyTrace B J :=
  {p with pins := p.pins.erase z}

private theorem splice_trace_cutOn {site : J → ComplexBits B} {H : J → ℕ → ComplexBits B}
    {m : B} {p : PolyTrace B J} (h : m ≤ polyValid site H p) :
    ∀ c ∈ p.coeff,c.CutOn m :=
  (le_coeffValue_iff _ _).mp (h.trans inf_le_left)

set_option maxHeartbeats 500000 in

theorem named_splice_common_refinement
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p₀ p₁ h : PolyTrace B J) (z : J) (m : B)
    (hSite : ∀ i,(site i).CutOn m)
    (hP₀ : m ≤ polyValid site H p₀) (hP₁ : m ≤ polyValid site H p₁)
    (hOld₀ : m ≤ (polynomialQ site H).refines (some h) (some (eraseSplicePin p₀ z)))
    (hOld₁ : m ≤ (polynomialQ site H).refines (some h) (some (eraseSplicePin p₁ z)))
    (hValZ : m ≤ (p₀.eval (site z)).name =ᴮ (p₁.eval (site z)).name)
    (hR : p₁.radius = p₀.radius) (hE : p₁.budget = p₀.budget)
    (G : NamedSpliceGuard site z (eraseSplicePin p₁ z).pins.toList p₀.radius m)
    (e d b : ℚ) (he : 0 ≤ e) (hd : 0 ≤ d) (hb : 0 < b)
    (hQuant : G.bound*e+d ≤ p₀.budget-b)
    (hTight : ∀ t : RatGrid p₀.radius,m ≤ distanceLe
      (h.eval (ComplexBits.checked (gridPoint t))) (p₀.eval (ComplexBits.checked (gridPoint t))) e)
    (hClose : ∀ t : RatGrid p₀.radius,m ≤ distanceLe
      (p₀.eval (ComplexBits.checked (gridPoint t))) (p₁.eval (ComplexBits.checked (gridPoint t))) d) :
    ∃ q : PolyTrace B J, q.pins = p₀.pins ∪ p₁.pins ∧ q.radius = p₀.radius ∧ q.budget = b ∧
      m ≤ (polynomialQ site H).refines (some q) (some p₀) ∧
      m ≤ (polynomialQ site H).refines (some q) (some p₁) := by
  classical
  let q : PolyTrace B J :=
    ⟨namedSpliceCoefficients p₀.coeff h.coeff G.coeff,p₀.pins ∪ p₁.pins,p₀.radius,b,hb⟩
  have hH : m ≤ polyValid site H h :=
    hOld₀.trans (((polynomialQ site H).refine_valid _ _).trans inf_le_left)
  have hEval (x : ComplexBits B) (hx : x.CutOn m) :
      m ≤ (q.eval x).name =ᴮ (spliceValue (p₀.eval x) (h.eval x) (mixedPolynomialEval G.coeff x)).name :=
    (namedSpliceCoefficients_eval p₀.coeff h.coeff G.coeff x m
      (splice_trace_cutOn hP₀) (splice_trace_cutOn hH) G.coeff_cut hx).2
  have hp0 (x : ComplexBits B) (hx : x.CutOn m) : (p₀.eval x).CutOn m :=
    mixedPolynomialEval_cutOn _ x (splice_trace_cutOn hP₀) hx
  have hp1 (x : ComplexBits B) (hx : x.CutOn m) : (p₁.eval x).CutOn m :=
    mixedPolynomialEval_cutOn _ x (splice_trace_cutOn hP₁) hx
  have hh0 (x : ComplexBits B) (hx : x.CutOn m) : (h.eval x).CutOn m :=
    mixedPolynomialEval_cutOn _ x (splice_trace_cutOn hH) hx
  have hGuard (x : ComplexBits B) (hx : x.CutOn m) : (mixedPolynomialEval G.coeff x).CutOn m :=
    mixedPolynomialEval_cutOn _ x G.coeff_cut hx
  have hQC : ∀ c ∈ q.coeff,c.CutOn m :=
    (namedSpliceCoefficients_eval p₀.coeff h.coeff G.coeff _ m
      (splice_trace_cutOn hP₀) (splice_trace_cutOn hH) G.coeff_cut (hSite z)).1
  have hq0 (x : ComplexBits B) (hx : x.CutOn m) : (q.eval x).CutOn m :=
    mixedPolynomialEval_cutOn _ x hQC hx
  have old0 (i : J) (hi : i ∈ p₀.pins) (hn : i ≠ z) :
      m ≤ (h.eval (site i)).name =ᴮ (p₀.eval (site i)).name := by
    have hm : i ∈ (eraseSplicePin p₀ z).pins := Finset.mem_erase.mpr ⟨hn,hi⟩
    have ht : m ≤ agreementValue site h (eraseSplicePin p₀ z) :=
      hOld₀.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact ht.trans (iInf_le (fun j : {j : J // j ∈ (eraseSplicePin p₀ z).pins} =>
      (h.eval (site j.val)).name =ᴮ ((eraseSplicePin p₀ z).eval (site j.val)).name) ⟨i,hm⟩)
  have old1 (i : J) (hi : i ∈ p₁.pins) (hn : i ≠ z) :
      m ≤ (h.eval (site i)).name =ᴮ (p₁.eval (site i)).name := by
    have hm : i ∈ (eraseSplicePin p₁ z).pins := Finset.mem_erase.mpr ⟨hn,hi⟩
    have ht : m ≤ agreementValue site h (eraseSplicePin p₁ z) :=
      hOld₁.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact ht.trans (iInf_le (fun j : {j : J // j ∈ (eraseSplicePin p₁ z).pins} =>
      (h.eval (site j.val)).name =ᴮ ((eraseSplicePin p₁ z).eval (site j.val)).name) ⟨i,hm⟩)
  have atZ : m ≤ (q.eval (site z)).name =ᴮ (p₀.eval (site z)).name :=
    bSet.bv_trans (hEval _ (hSite z)) (spliceValue_eq_on (hp0 _ (hSite z)) (hh0 _ (hSite z))
      (hGuard _ (hSite z)) false (Or.inl G.at_new))
  have eq0 (i : J) (hi : i ∈ p₀.pins) : m ≤ (q.eval (site i)).name =ᴮ (p₀.eval (site i)).name := by
    by_cases heq : i = z
    · simpa only [heq] using atZ
    · exact bSet.bv_trans (hEval _ (hSite i))
        (spliceValue_eq_on (hp0 _ (hSite i)) (hh0 _ (hSite i)) (hGuard _ (hSite i))
          false (Or.inr (old0 i hi heq)))
  have eq1 (i : J) (hi : i ∈ p₁.pins) : m ≤ (q.eval (site i)).name =ᴮ (p₁.eval (site i)).name := by
    by_cases heq : i = z
    · rw [heq]
      exact bSet.bv_trans atZ hValZ
    · have hPin : i ∈ (eraseSplicePin p₁ z).pins.toList :=
        Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨heq,hi⟩)
      exact bSet.bv_trans (hEval _ (hSite i))
        (bSet.bv_trans
          (spliceValue_eq_on (hp0 _ (hSite i)) (hh0 _ (hSite i)) (hGuard _ (hSite i))
            true (G.at_old i hPin)) (old1 i hi heq))
  have hQ : m ≤ polyValid site H q := by
    unfold polyValid
    refine le_inf ((le_coeffValue_iff _ _).mpr hQC) ?_
    unfold paletteValue
    apply le_iInf
    intro i
    have pal (p : PolyTrace B J) (hP : m ≤ polyValid site H p)
        (hi : i.1 ∈ p.pins) (hEQ : m ≤ (q.eval (site i.1)).name =ᴮ (p.eval (site i.1)).name) :
        m ≤ ⨆ n : ℕ, (q.eval (site i.1)).name =ᴮ (H i.1 n).name := by
      have hv : m ≤ ⨆ n : ℕ, (p.eval (site i.1)).name =ᴮ (H i.1 n).name :=
        (hP.trans inf_le_right).trans (iInf_le (fun j : {j : J // j ∈ p.pins} =>
          ⨆ n : ℕ, (p.eval (site j.val)).name =ᴮ (H j.val n).name) ⟨i.1,hi⟩)
      apply (le_inf hEQ hv).trans
      rw [inf_iSup_eq]
      exact iSup_le fun n => le_iSup_of_le n (bSet.bv_trans inf_le_left inf_le_right)
    rcases Finset.mem_union.mp i.2 with hj|hj
    · exact pal p₀ hP₀ hj (eq0 i.1 hj)
    · exact pal p₁ hP₁ hj (eq1 i.1 hj)
  have hL : 0 ≤ G.bound := zero_le_one.trans G.bound_one
  have hd0 : 0 ≤ G.bound*e := mul_nonneg hL he
  have hB₀ : b ≤ p₀.budget := by linarith
  have hB₁ : b ≤ p₁.budget := by rw [hE]; exact hB₀
  have hNear₀ (t : RatGrid p₀.radius) :
      m ≤ distanceLe (q.eval (ComplexBits.checked (gridPoint t)))
        (p₀.eval (ComplexBits.checked (gridPoint t))) (G.bound*e) := by
    let x := ComplexBits.checked (B := B) (gridPoint t)
    have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
    exact extend_same_mark_seed_error
      (spliceValue_cutOn (hp0 _ hx) (hh0 _ hx) (hGuard _ hx)) (hq0 _ hx) (hp0 _ hx)
      (bSet.bv_symm (hEval _ hx)) hd0
      (spliceValue_distance_left (hp0 _ hx) (hh0 _ hx) (hGuard _ hx) G.bound e hL he
        (G.grid_bound t) (hTight t))
  have hNear₁ (t : RatGrid p₀.radius) :
      m ≤ distanceLe (q.eval (ComplexBits.checked (gridPoint t)))
        (p₁.eval (ComplexBits.checked (gridPoint t))) (G.bound*e+d) := by
    let x := ComplexBits.checked (B := B) (gridPoint t)
    have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
    exact distanceLe_triangle (hq0 _ hx) (hp0 _ hx) (hp1 _ hx)
      hd0 hd (hNear₀ t) (hClose t)
  refine ⟨q,rfl,rfl,rfl,?_,?_⟩
  · change m ≤ (polyValid site H q ⊓ polyValid site H p₀) ⊓ refinesValue site q p₀
    refine le_inf (le_inf hQ hP₀) (le_inf ?_ (le_inf ?_ ?_))
    · have hc : p₀.pins ⊆ q.pins ∧ q.budget ≤ p₀.budget ∧ p₀.radius ≤ q.radius :=
        ⟨fun _ hj => Finset.mem_union.mpr (Or.inl hj),hB₀,le_rfl⟩
      simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hc,le_top]
    · exact le_iInf fun j => eq0 j.1 j.2
    · apply le_iInf
      intro t
      let x := ComplexBits.checked (B := B) (gridPoint t)
      have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
      exact distanceLe_mono (hq0 _ hx) (hp0 _ hx) hd0 (by linarith) (hNear₀ t)
  · change m ≤ (polyValid site H q ⊓ polyValid site H p₁) ⊓ refinesValue site q p₁
    refine le_inf (le_inf hQ hP₁) (le_inf ?_ (le_inf ?_ ?_))
    · have hc : p₁.pins ⊆ q.pins ∧ q.budget ≤ p₁.budget ∧ p₁.radius ≤ q.radius :=
        ⟨fun _ hj => Finset.mem_union.mpr (Or.inr hj),hB₁,le_of_eq hR⟩
      simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hc,le_top]
    · exact le_iInf fun j => eq1 j.1 j.2
    · unfold discValue
      rw [hR,hE]
      apply le_iInf
      intro t
      let x := ComplexBits.checked (B := B) (gridPoint t)
      have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
      exact distanceLe_mono (hq0 _ hx) (hp1 _ hx) (add_nonneg hd0 hd) hQuant (hNear₁ t)

end JSP000930.Negative
