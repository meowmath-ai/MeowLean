import JSP000930NegativePolynomialDistance

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure NamedPolynomialTower (B : Type) where
  Label : ℕ → Type
  active : ∀ t,Label t → B
  coeff : ∀ t,Label t → List (ComplexBits B)

structure NamedPolynomialTower.On (T : NamedPolynomialTower B) (m : B) : Prop where
  cover : ∀ t,m ≤ ⨆ l,T.active t l
  proper : ∀ t l c,c ∈ T.coeff t l → c.CutOn (m ⊓ T.active t l)
  gridCauchy : ∀ R : ℕ, 1 ≤ R → ∀ e : ℚ, 0 < e →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ (l : T.Label i) (r : T.Label j) (g : RatGrid R),
      m ⊓ (T.active i l ⊓ T.active j r) ≤ distanceLe
        (mixedPolynomialEval (T.coeff i l) (ComplexBits.checked (gridPoint g)))
        (mixedPolynomialEval (T.coeff j r) (ComplexBits.checked (gridPoint g))) e

noncomputable def NamedPolynomialTower.coefficient (T : NamedPolynomialTower B) (t k : ℕ) : ComplexBits B :=
  chosenPolyCoeff (T.active t) (T.coeff t) k

theorem NamedPolynomialTower.coefficient_proper (T : NamedPolynomialTower B) (m : B)
    (h : T.On m) (t k : ℕ) : (T.coefficient t k).CutOn m :=
  chosenPolyCoeff_cutOn (T.active t) (T.coeff t) m (h.cover t) (h.proper t) k

theorem NamedPolynomialTower.coeffDistance (T : NamedPolynomialTower B) (m : B) (h : T.On m)
    (R : ℕ) (hR : 0 < R) (e : ℚ) (he : 0 < e) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ k : ℕ,
      m ≤ distanceLe (T.coefficient i k) (T.coefficient j k) (e/(R : ℚ)^k) := by
  obtain ⟨N,hN⟩ := h.gridCauchy (R+1) (by omega) e he
  refine ⟨N,fun i j hi hj k => ?_⟩
  let u (l : T.Label i) := firstChoiceCell (T.active i) l
  let v (r : T.Label j) := firstChoiceCell (T.active j) r
  have hu : m ≤ ⨆ l,u l := by simpa only [u,iSup_firstChoiceCell] using h.cover i
  have hv : m ≤ ⨆ r,v r := by simpa only [v,iSup_firstChoiceCell] using h.cover j
  apply (le_inf le_rfl (le_inf hu hv)).trans
  rw [iSup_inf_eq,inf_iSup_eq]
  refine iSup_le fun l => ?_
  rw [inf_iSup_eq,inf_iSup_eq]
  refine iSup_le fun r => ?_
  let s := m ⊓ (u l ⊓ v r)
  let P := T.coeff i l
  let Q := T.coeff j r
  have hsm : s ≤ m := inf_le_left
  have hsI : s ≤ u l := inf_le_right.trans inf_le_left
  have hsJ : s ≤ v r := inf_le_right.trans inf_le_right
  have hsi : s ≤ m ⊓ T.active i l := le_inf hsm (hsI.trans (firstChoiceCell_le_active _ _))
  have hsj : s ≤ m ⊓ T.active j r := le_inf hsm (hsJ.trans (firstChoiceCell_le_active _ _))
  have hp : ∀ c ∈ P,c.CutOn s := fun c hc =>
    JSP000930.AnalyticSyntax.complexCutOn_mono hsi (h.proper i l c hc)
  have hq : ∀ c ∈ Q,c.CutOn s := fun c hc =>
    JSP000930.AnalyticSyntax.complexCutOn_mono hsj (h.proper j r c hc)
  have hd (g : RatGrid (R+1)) : s ≤ distanceLe
      (mixedPolynomialEval P (ComplexBits.checked (gridPoint g)))
      (mixedPolynomialEval Q (ComplexBits.checked (gridPoint g))) e :=
    (le_inf hsm (le_inf (hsI.trans (firstChoiceCell_le_active _ _))
      (hsJ.trans (firstChoiceCell_le_active _ _)))).trans (hN i j hi hj l r g)
  apply distanceLe_congr_of_named_eq
    (JSP000930.AnalyticSyntax.complexCutOn_mono hsm (T.coefficient_proper m h i k))
    (JSP000930.AnalyticSyntax.complexCutOn_mono hsm (T.coefficient_proper m h j k))
    (zeroPaddedPoly_cutOn P s hp k) (zeroPaddedPoly_cutOn Q s hq k) (by positivity)
  · exact hsI.trans (JSP000930.Positive.sameMaskedComplex_name
      (chosenPolyCoeff_on_cell (T.active i) (T.coeff i) k l))
  · exact hsJ.trans (JSP000930.Positive.sameMaskedComplex_name
      (chosenPolyCoeff_on_cell (T.active j) (T.coeff j) k r))
  · exact coefficient_distance_from_grid P Q s hp hq R hR e he.le hd k

theorem NamedPolynomialTower.coeffCauchy
    (T : NamedPolynomialTower B) (m : B) (h : T.On m)
    (k : ℕ) (b : Bool) (ε : ℚ) (hε : 0 < ε) :
    m ≤ ⨆ N : ℕ,cutCauchyTail (fun n => (T.coefficient n k).coord b) ε N := by
  obtain ⟨N,hN⟩ := T.coeffDistance m h 1 zero_lt_one (ε/2) (by positivity)
  apply le_iSup_of_le N
  unfold cutCauchyTail
  refine le_iInf fun i => le_iInf fun j => ?_
  have hDist := hN i.val j.val i.property j.property k
  have hDis : m ≤ distanceLe (T.coefficient i.val k) (T.coefficient j.val k) (ε/2) := by
    simpa only [Nat.cast_one,one_pow,div_one] using hDist
  exact coordNear_of_named_distanceLe
    (T.coefficient_proper m h i.val k) (T.coefficient_proper m h j.val k)
    (by positivity) (by linarith) hDis b

noncomputable def NamedPolynomialTower.limitCoefficients (T : NamedPolynomialTower B) (k : ℕ) :
    ComplexBits B :=
  ⟨roundedLiminfBits (fun n => (T.coefficient n k).re),
   roundedLiminfBits (fun n => (T.coefficient n k).im)⟩

theorem NamedPolynomialTower.limit_coeff_proper
    (T : NamedPolynomialTower B) (m : B) (h : T.On m) (k : ℕ) :
    (T.limitCoefficients k).CutOn m := by
  have oneCoord (b : Bool) : ProperCutOn m ((T.limitCoefficients k).coord b) := by
    let u (n : ℕ) := (T.coefficient n k).coord b
    have hX (n : ℕ) : ProperCutOn m (u n) := by
      have hU := T.coefficient_proper m h n k
      cases b
      · exact hU.1
      · exact hU.2
    have hEq : (T.limitCoefficients k).coord b = roundedLiminfBits u := by cases b <;> rfl
    rw [hEq]
    obtain ⟨hn,hp⟩ := cutCauchy_limit_proper_nonempty u m
      (T.coeffCauchy m h k b 1 zero_lt_one) (fun n => (hX n).1) (fun n => (hX n).2.1)
    refine ⟨hn,hp,?_,?_⟩
    · exact fun q r hr => inf_le_right.trans (roundedLiminfBits_downward u hr)
    · exact fun q => inf_le_right.trans_eq (roundedLiminfBits_rounded u q)
  exact ⟨oneCoord false,oneCoord true⟩

theorem NamedPolynomialTower.limit_coeff_converges
    (T : NamedPolynomialTower B) (m : B) (h : T.On m)
    (k : ℕ) (b : Bool) (ε : ℚ) (he : 0 < ε) :
    m ≤ ⨆ N : ℕ,cutConvergesTail (fun n => (T.coefficient n k).coord b)
      ((T.limitCoefficients k).coord b) ε N := by
  let u (n : ℕ) := (T.coefficient n k).coord b
  have hEq : (T.limitCoefficients k).coord b = roundedLiminfBits u := by cases b <;> rfl
  rw [hEq]
  exact cutCauchy_roundedLiminf_converges u m (fun e he' => T.coeffCauchy m h k b e he') ε he

end JSP000930.Negative
