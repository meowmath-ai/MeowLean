import JSP000930SymbolicSupportedForcing

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def PolyTrace.trimPins (p : PolyTrace B J) (l : Finset J) : PolyTrace B J :=
  { p with pins := l }

theorem valid_trimPins_mono (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) (l : Finset J) (hl : l ⊆ p.pins) :
    polyValid site H p ≤ polyValid site H (p.trimPins l) := by
  unfold polyValid
  apply inf_le_inf le_rfl
  unfold paletteValue
  apply le_iInf
  intro j
  exact iInf_le _ (⟨j.1,hl j.2⟩ : {v : J // v ∈ p.pins})

theorem structural_of_weighted_refines (site : J → ComplexBits B) (q p : PolyTrace B J)
    (m : B) (hm : m ≠ ⊥) (h : m ≤ refinesValue site q p) :
    p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧ p.radius ≤ q.radius := by
  classical
  by_contra hc
  have hFalse : m ≤ JSP000933.PositiveForcing.crispTruth B (p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧
      p.radius ≤ q.radius) := h.trans inf_le_left
  rw [JSP000933.PositiveForcing.crispTruth,ite_eq_right hc] at hFalse
  exact hm (le_bot_iff.mp hFalse)

theorem refines_trimPins (site : J → ComplexBits B) (q p : PolyTrace B J)
    (m : B) (hm : m ≠ ⊥) (h : m ≤ refinesValue site q p)
    (l : Finset J) (hl : p.pins ⊆ l) :
    m ≤ refinesValue site (q.trimPins l) p := by
  classical
  obtain ⟨_,he,hR⟩ := structural_of_weighted_refines site q p m hm h
  have hnum : p.pins ⊆ (q.trimPins l).pins ∧ (q.trimPins l).budget ≤ p.budget ∧
      p.radius ≤ (q.trimPins l).radius := ⟨hl,he,hR⟩
  unfold refinesValue
  refine le_inf ?_ ?_
  · simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hnum,le_top]
  · exact h.trans inf_le_right

def polyLabelPins (p : Option (PolyTrace B J)) : Finset J :=
  match p with
  | none => ∅
  | some p => p.pins

theorem polyLabelPins_subset_of_refines (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (r : PolyTrace B J) (p : Option (PolyTrace B J)) (m : B) (hm : m ≠ ⊥)
    (h : m ≤ (polynomialQ site H).refines (some r) p) : polyLabelPins p ⊆ r.pins := by
  cases p with
  | none => exact Finset.empty_subset _
  | some p =>
    exact (structural_of_weighted_refines site r p m hm (h.trans inf_le_right)).1

theorem trim_refines_polyLabel (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (r : PolyTrace B J) (p : Option (PolyTrace B J)) (m : B) (hm : m ≠ ⊥)
    (h : m ≤ (polynomialQ site H).refines (some r) p)
    (l : Finset J) (hl : polyLabelPins p ⊆ l) (hr : l ⊆ r.pins) :
    m ≤ (polynomialQ site H).refines (some (r.trimPins l)) p := by
  have hV : m ≤ polyValid site H (r.trimPins l) :=
    (h.trans (((polynomialQ site H).refine_valid _ _).trans inf_le_left)).trans
      (valid_trimPins_mono site H r l hr)
  cases p with
  | none => exact hV
  | some p =>
    change m ≤ (polyValid site H (r.trimPins l) ⊓ polyValid site H p) ⊓
      refinesValue site (r.trimPins l) p
    exact le_inf (le_inf hV (h.trans (inf_le_left.trans inf_le_right)))
      (refines_trimPins site r p m hm (h.trans inf_le_right) l hl)

end JSP000930.Negative
