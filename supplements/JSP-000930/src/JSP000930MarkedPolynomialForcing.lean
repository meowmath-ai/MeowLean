import JSP000930PolynomialRefinementLaws
import JSP000933MarkedTotalForcing

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def polyLabelValid (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) : Option (PolyTrace B J) → B
  | none => ⊤
  | some p => polyValid site H p

noncomputable def polyLabelRefines (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) :
    Option (PolyTrace B J) → Option (PolyTrace B J) → B
  | none, none => ⊤
  | some p, none => polyValid site H p
  | none, some _ => ⊥
  | some q, some p =>
      (polyValid site H q ⊓ polyValid site H p) ⊓ refinesValue site q p

noncomputable def polynomialQ (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) : ValuedPoset B (Option (PolyTrace B J)) where
  valid := polyLabelValid site H
  refines := polyLabelRefines site H
  refine_valid := by
    intro p q
    cases p <;> cases q <;> simp only [polyLabelValid, polyLabelRefines, inf_top_eq,
      top_inf_eq, le_rfl, bot_le]
    exact inf_le_left
  refl := by
    intro p
    cases p with
    | none => exact le_rfl
    | some p =>
      change polyValid site H p ≤
        (polyValid site H p ⊓ polyValid site H p) ⊓ refinesValue site p p
      exact le_inf (le_inf le_rfl le_rfl)
        (refinesValue_refl site p (show polyValid site H p ≤ coeffValue p.coeff from inf_le_left))
  trans := by
    intro r q p
    cases r <;> cases q <;> cases p <;>
      simp only [polyLabelRefines, bot_inf_eq, inf_bot_eq, inf_top_eq,
        top_inf_eq, le_rfl, bot_le, le_top]
    case some.some.none r q =>
      exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    case some.some.some r q p =>
      let v := ((polyValid site H r ⊓ polyValid site H q) ⊓ refinesValue site r q) ⊓
        ((polyValid site H q ⊓ polyValid site H p) ⊓ refinesValue site q p)
      change v ≤ (polyValid site H r ⊓ polyValid site H p) ⊓ refinesValue site r p
      have hr : v ≤ polyValid site H r := inf_le_left.trans (inf_le_left.trans inf_le_left)
      have hq : v ≤ polyValid site H q := inf_le_left.trans (inf_le_left.trans inf_le_right)
      have hp : v ≤ polyValid site H p := inf_le_right.trans (inf_le_left.trans inf_le_right)
      have hr' : v ≤ coeffValue r.coeff := hr.trans inf_le_left
      have hq' : v ≤ coeffValue q.coeff := hq.trans inf_le_left
      have hp' : v ≤ coeffValue p.coeff := hp.trans inf_le_left
      exact le_inf (le_inf hr hp)
        (refinesValue_trans site r q p hr' hq' hp'
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  weakest := none
  weakest_valid := rfl
  weaker := by
    intro p
    cases p <;> exact le_rfl

theorem map_polyLabelValid (F : CompleteValueMap B C) (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : Option (PolyTrace B J)) :
    F.toFun ((polynomialQ site H).valid p) =
      (polynomialQ (fun z => (site z).map F) (fun z n => (H z n).map F)).valid
        (p.map (PolyTrace.map F)) := by
  cases p with
  | none => exact F.map_top
  | some p => exact map_polyValid F site H p

theorem map_polyLabelRefines (F : CompleteValueMap B C) (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (q p : Option (PolyTrace B J)) :
    F.toFun ((polynomialQ site H).refines q p) =
      (polynomialQ (fun z => (site z).map F) (fun z n => (H z n).map F)).refines
        (q.map (PolyTrace.map F)) (p.map (PolyTrace.map F)) := by
  cases q <;> cases p <;>
    simp only [polynomialQ, polyLabelRefines, Option.map_none, Option.map_some,
      F.map_bot, F.map_top, F.map_inf, map_polyValid, map_refinesValue]

end JSP000930.Negative
