import JSP000930NegativeCountableNamedCenterBins
import JSP000930SymbolicTrimCommonRefinement

open bSet Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def NamedRowAt (A : J → Prop) (p : Option (PolyTrace B J)) : Prop :=
  ∀ j ∈ polyLabelPins p,A j

abbrev SupportedNamedRow (B J : Type) (A : J → Prop) :=
  {p : Option (PolyTrace B J) // NamedRowAt A p}

noncomputable def supportedNamedRowQ (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (A : J → Prop) :
    ValuedPoset B (SupportedNamedRow B J A) where
  valid p := (polynomialQ site H).valid p.val
  refines p q := (polynomialQ site H).refines p.val q.val
  refine_valid _ _ := (polynomialQ site H).refine_valid _ _
  refl _ := (polynomialQ site H).refl _
  trans _ _ _ := (polynomialQ site H).trans _ _ _
  weakest := ⟨none,by simp [NamedRowAt,polyLabelPins]⟩
  weakest_valid := rfl
  weaker _ := (polynomialQ site H).weaker _

noncomputable def tightErasedSplice (p : PolyTrace B J) (z : J) (G : ℚ)
    (hG : 1 ≤ G) : PolyTrace B J :=
  { eraseSplicePin p z with
    budget := p.budget/(4*G)
    budget_pos := div_pos p.budget_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hG)) }

theorem erase_mem_old {A : J → Prop} {p : PolyTrace B J} {z : J}
    (h : NamedRowAt (fun j => A j ∨ j = z) (some p)) :
    NamedRowAt A (some (eraseSplicePin p z)) := by
  intro j hj
  obtain ⟨hn,hp⟩ := Finset.mem_erase.mp hj
  exact (h j hp).resolve_right hn

theorem tightErasedSplice_valid (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) (z : J)
    (G : ℚ) (hG : 1 ≤ G) :
    polyValid site H p ≤ polyValid site H (tightErasedSplice p z G hG) :=
  valid_trimPins_mono site H p _ (Finset.erase_subset _ _)

theorem erased_of_tight_refinement (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p h : PolyTrace B J) (z : J)
    (G : ℚ) (hG : 1 ≤ G) {m : B} (hm : m ≠ ⊥)
    (hRef : m ≤ (polynomialQ site H).refines (some h) (some (tightErasedSplice p z G hG))) :
    (m ≤ (polynomialQ site H).refines (some h) (some (eraseSplicePin p z))) ∧
    (∀ g : RatGrid p.radius,m ≤ distanceLe (h.eval (ComplexBits.checked (gridPoint g)))
        (p.eval (ComplexBits.checked (gridPoint g))) (p.budget/(4*G))) := by
  let a := tightErasedSplice p z G hG
  have ha : m ≤ polyValid site H a := hRef.trans (inf_le_left.trans inf_le_right)
  have hh : m ≤ polyValid site H h := hRef.trans (inf_le_left.trans inf_le_left)
  have h₀ : m ≤ refinesValue site h a := hRef.trans inf_le_right
  have hgpos : 0 < G := zero_lt_one.trans_le hG
  have hBudget : a.budget ≤ p.budget := by
    change p.budget/(4*G) ≤ p.budget
    apply (div_le_iff₀ (mul_pos (by norm_num) hgpos)).mpr
    nlinarith [p.budget_pos, mul_nonneg p.budget_pos.le (show 0 ≤ 4*G-1 by linarith)]
  obtain ⟨hPin,he,hR⟩ := structural_of_weighted_refines site h a m hm h₀
  have hFine (g : RatGrid p.radius) : m ≤ distanceLe (h.eval (ComplexBits.checked (gridPoint g)))
      (p.eval (ComplexBits.checked (gridPoint g))) (a.budget-h.budget) :=
    (h₀.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ g)
  have hProper (g : RatGrid p.radius) :
      (h.eval (ComplexBits.checked (gridPoint g))).CutOn m ∧
      (p.eval (ComplexBits.checked (gridPoint g))).CutOn m :=
    ⟨eval_cutOn_of_coeff (hh.trans inf_le_left) (ComplexBits.checked_cutOn _ _),
      eval_cutOn_of_coeff (ha.trans inf_le_left) (ComplexBits.checked_cutOn _ _)⟩
  refine ⟨le_inf (le_inf hh ha) (le_inf ?_ (le_inf ?_ ?_)),?_⟩
  · change m ≤ JSP000933.PositiveForcing.crispTruth B ((eraseSplicePin p z).pins ⊆ h.pins ∧
      h.budget ≤ p.budget ∧ p.radius ≤ h.radius)
    have hStruct : (eraseSplicePin p z).pins ⊆ h.pins ∧
        h.budget ≤ p.budget ∧ p.radius ≤ h.radius := ⟨hPin,he.trans hBudget,hR⟩
    simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hStruct,le_top]
  · exact h₀.trans (inf_le_right.trans inf_le_left)
  · apply le_iInf
    intro g
    exact distanceLe_mono (hProper g).1 (hProper g).2 (sub_nonneg.mpr he)
      (sub_le_sub_right hBudget _) (hFine g)
  · intro g
    exact distanceLe_mono (hProper g).1 (hProper g).2 (sub_nonneg.mpr he)
      (sub_le_self _ h.budget_pos.le) (hFine g)

end JSP000930.Negative
