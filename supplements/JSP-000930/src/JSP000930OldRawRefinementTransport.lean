import JSP000930FreshActualCenterPlans

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem map_polyValid_on_pins {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (p : PolyTrace B J) (hp : ∀ j ∈ p.pins,A j) :
    F.toFun (polyValid site H p) = polyValid site' H' (p.map F) := by
  rw [map_polyValid]
  unfold polyValid
  apply congrArg (fun x : C => coeffValue (p.map F).coeff ⊓ x)
  exact paletteValue_eq_on_pins _ _ _ _ _ (fun j hj => hS j (hp j hj))
    (fun j hj => hH j (hp j hj))

theorem map_raw_supported_refines {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (q p : PolyTrace B J) (hq : ∀ j ∈ q.pins,A j) (hp : ∀ j ∈ p.pins,A j) :
    F.toFun ((polynomialQ site H).refines (some q) (some p)) =
      (polynomialQ site' H').refines (some (q.map F)) (some (p.map F)) := by
  change F.toFun ((polyValid site H q ⊓ polyValid site H p) ⊓ refinesValue site q p) =
    (polyValid site' H' (q.map F) ⊓ polyValid site' H' (p.map F)) ⊓
      refinesValue site' (q.map F) (p.map F)
  have hr := map_refinesValue F site q p
  simp only [F.map_inf,hr,map_polyValid_on_pins F site H site' H' hS hH q hq,
    map_polyValid_on_pins F site H site' H' hS hH p hp]
  unfold refinesValue
  rw [agreementValue_eq_on_pins _ _ _ site' (fun j hj => hS j (hp j hj))]

end JSP000930.Negative
