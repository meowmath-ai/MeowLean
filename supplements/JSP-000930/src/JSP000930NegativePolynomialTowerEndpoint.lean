import JSP000930NegativePolynomialNamedGrid

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000933.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedPolynomialTower.On.mono {T : NamedPolynomialTower B} {p q : B}
    (h : T.On p) (hq : q ≤ p) : T.On q := by
  constructor
  · exact fun t => hq.trans (h.cover t)
  · intro t l c hc
    exact complexCutOn_mono (inf_le_inf_right _ hq) (h.proper t l c hc)
  · intro R hR e he
    obtain ⟨N,hN⟩ := h.gridCauchy R hR e he
    exact ⟨N,fun i j hi hj l r g =>
      (inf_le_inf_right _ hq).trans (hN i j hi hj l r g)⟩

private theorem sameComplex_restrict {p q : B} {a b : ComplexBits B}
    (hpq : p ≤ q) (h : JSP000930.Positive.sameMaskedComplex q a b) :
    JSP000930.Positive.sameMaskedComplex p a b := by
  have hp : p ⊓ q = p := inf_eq_left.mpr hpq
  constructor
  · intro t
    calc
      p ⊓ a.re t = p ⊓ (q ⊓ a.re t) := by rw [← inf_assoc,hp]
      _ = p ⊓ (q ⊓ b.re t) := by rw [h.1 t]
      _ = p ⊓ b.re t := by rw [← inf_assoc,hp]
  · intro t
    calc
      p ⊓ a.im t = p ⊓ (q ⊓ a.im t) := by rw [← inf_assoc,hp]
      _ = p ⊓ (q ⊓ b.im t) := by rw [h.2 t]
      _ = p ⊓ b.im t := by rw [← inf_assoc,hp]

theorem NamedPolynomialTower.stage_eval_eq_horner_on_cell (T : NamedPolynomialTower B)
    (m : B) (h : T.On m) (t : ℕ) (l : T.Label t) (z : ComplexBits B) (p : B)
    (hp : p ≤ m) (hc : p ≤ firstChoiceCell (T.active t) l) (hz : z.CutOn p) :
    p ≤ (taylorLimitBits (T.coefficient t) z).name =ᴮ (mixedPolynomialEval (T.coeff t l) z).name := by
  have hL : p ≤ m ⊓ T.active t l := le_inf hp (hc.trans (firstChoiceCell_le_active _ _))
  have hf : ∀ c ∈ T.coeff t l,c.CutOn p :=
    fun c hm => complexCutOn_mono hL (h.proper t l c hm)
  have hMask (n : ℕ) : JSP000930.Positive.sameMaskedComplex p
      (T.coefficient t n) (zeroPaddedPoly (T.coeff t l) n) :=
    sameComplex_restrict hc (chosenPolyCoeff_on_cell (T.active t) (T.coeff t) n l)
  exact bSet.bv_trans (JSP000930.Positive.sameMaskedComplex_name
    (JSP000930.Positive.sameMaskedComplex_taylorLimit hMask
      (JSP000930.Positive.sameMaskedComplex_self p z)))
    (zeroPaddedPoly_limit_eq_horner (T.coeff t l) z p hf hz)

theorem named_eq_of_arbitrary_distance {p : B} {u v : ComplexBits B}
    (hu : u.CutOn p) (hv : v.CutOn p)
    (h : ∀ e : ℚ,0 < e → p ≤ distanceLe u v e) : p ≤ u.name =ᴮ v.name := by
  let W (b : Bool) : ComplexBits B := if b then v else u
  have hW (b : Bool) : (W b).CutOn p := by cases b; exact hu; exact hv
  refine complexEq_of_decision_law W p hW u v hu hv ?_
  intro q w hq hn hqp ht
  have heq : w false = w true := by
    by_contra hne
    have hdist : 0 < dist (w false) (w true) := dist_pos.mpr hne
    obtain ⟨e,he,hle⟩ := exists_rat_btwn hdist
    have he' : 0 < e := by exact_mod_cast he
    have hh := trace_distanceLe hq hn hqp hu hv (ht false) (ht true) he'.le (h e he')
    exact (not_le_of_gt hle) hh
  refine ⟨w false,ht false,?_⟩
  rw [heq]
  exact ht true

theorem NamedPolynomialTower.limit_eq_of_stage_approximation
    (T : NamedPolynomialTower B) (m : B) (h : T.On m) (z w : ComplexBits B)
    (hz : z.CutOn m) (hw : w.CutOn m)
    (hApprox : ∀ e : ℚ,0 < e → ∃ N : ℕ,∀ t ≥ N,
      m ≤ distanceLe (taylorLimitBits (T.coefficient t) z) w e) :
    m ≤ (taylorLimitBits T.limitCoefficients z).name =ᴮ w.name := by
  let u := taylorLimitBits T.limitCoefficients z
  have hu : u.CutOn m := taylorLimitBits_cutOn _ _ _ (T.limit_coeff_proper m h) hz (T.limitGrowth m h)
  refine named_eq_of_arbitrary_distance hu hw ?_
  intro e he
  have hR := halfRadiusBound_cover z m hz
  apply (le_inf le_rfl hR).trans
  rw [inf_iSup_eq]
  refine iSup_le fun R => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun hRpos => ?_
  let p := m ⊓ halfRadiusBound z R
  have hp : p ≤ m := inf_le_left
  have h' := h.mono hp
  have hZ := complexCutOn_mono hp hz
  have hW := complexCutOn_mono hp hw
  obtain ⟨N,hN⟩ := T.eval_stage_distance p h' z hZ R (by omega) inf_le_right (e/4) (by positivity)
  obtain ⟨M,hM⟩ := hApprox (e/2) (by positivity)
  let t := max N M
  have hMid := taylorLimitBits_cutOn (T.coefficient t) z p
    (T.coefficient_proper p h' t) hZ (T.stageGrowth p h' t)
  have hBound := distanceLe_triangle (complexCutOn_mono hp hu) hMid hW
    (show 0 ≤ 2*(e/4) by positivity) (show 0 ≤ e/2 by positivity)
    (hN t (le_max_left _ _)) (hp.trans (hM t (le_max_right _ _)))
  rw [show 2 * (e / 4) + e / 2 = e by ring] at hBound
  exact hBound

noncomputable def towerLimitCodeBits (T : NamedPolynomialTower B) : JSP000930.Positive.TaylorSlot → B :=
  fun j => (T.limitCoefficients j.1).coord j.2.1 j.2.2

noncomputable def towerLimitCodeName (T : NamedPolynomialTower B) : bSet B :=
  JSP000930.Positive.taylorCodeName (towerLimitCodeBits T)

theorem towerLimitCode_forces_entire {n : ℕ} (v : DVec (V B) n) (A : STerm n)
    (T : NamedPolynomialTower B) (p : B) (hA : bTerm v A = towerLimitCodeName T)
    (h : T.On p) : p ≤ bTruth v (isEntireCode_f A) :=
  JSP000930.Positive.canonical_native_data_forces_entire v A (towerLimitCodeBits T) p hA
    (T.limit_coeff_proper p h) (T.limitGrowth p h)

theorem towerLimitCode_eval_iff {n : ℕ} (v : DVec (V B) n) (A Z Y : STerm n)
    (T : NamedPolynomialTower B) (z : ComplexBits B) (p : B)
    (hA : bTerm v A = towerLimitCodeName T) (hZ : bTerm v Z = z.name)
    (h : T.On p) (hz : z.CutOn p) :
    p ≤ bTruth v (evalAt_f A Z Y) ↔
      p ≤ bTerm v Y =ᴮ (taylorLimitBits T.limitCoefficients z).name := by
  have hE := towerLimitCode_forces_entire v A T p hA h
  have hS : p ≤ bTruth v (sequence_f A) := by
    simp only [isEntireCode_f,boolean_realize_bounded_formula_and] at hE
    exact hE.trans inf_le_left
  have hm := JSP000930.Positive.canonical_sequence_bits_mask v A (towerLimitCodeBits T) p hA hS
  have he := JSP000930.Positive.sameMaskedComplex_name
    (JSP000930.Positive.sameMaskedComplex_taylorLimit hm
      (JSP000930.Positive.sameMaskedComplex_self p z))
  exact (forces_evalAt_iff_taylorLimit v A Z Y z p hZ hz hE).trans
    ⟨fun h => bSet.bv_trans h he,fun h => bSet.bv_trans h (he.trans_eq bSet.bv_eq_symm)⟩

end JSP000930.Negative
