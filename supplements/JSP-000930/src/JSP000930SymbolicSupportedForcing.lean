import JSP000930SymbolicFiniteSupport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem paletteValue_eq_on_pins (p : PolyTrace B J)
    (site site' : J → ComplexBits B) (H H' : J → ℕ → ComplexBits B)
    (hS : ∀ j ∈ p.pins,site j = site' j)
    (hH : ∀ j ∈ p.pins,∀ n,H j n = H' j n) :
    paletteValue site H p = paletteValue site' H' p := by
  unfold paletteValue
  apply iInf_congr
  intro j
  rw [hS j.1 j.2]
  apply iSup_congr
  intro n
  rw [hH j.1 j.2 n]

theorem agreementValue_eq_on_pins (q p : PolyTrace B J)
    (site site' : J → ComplexBits B) (hS : ∀ j ∈ p.pins,site j = site' j) :
    agreementValue site q p = agreementValue site' q p := by
  unfold agreementValue
  apply iInf_congr
  intro j
  rw [hS j.1 j.2]

theorem symbolicPolyValid_partial_map {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (p : SymbolicTrace J) (hP : SymbolicAt A p) :
    F.toFun (polyValid site H (decodeSymbolicTrace site H p)) =
      polyValid site' H' (decodeSymbolicTrace site' H' p) := by
  have ht := decodeSymbolicTrace_completeMap_on_log F p site H site' H'
    (fun i hi => hS i (hP i hi)) (fun i hi => hH i (hP i hi))
  rw [map_polyValid,ht]
  unfold polyValid
  apply congrArg (fun x : C => coeffValue (decodeSymbolicTrace site' H' p).coeff ⊓ x)
  exact paletteValue_eq_on_pins _ _ _ _ _
    (fun i hi => hS i (allowed_of_decode_pin site' H' p hP hi))
    (fun i hi => hH i (allowed_of_decode_pin site' H' p hP hi))

theorem symbolicRefines_partial_map {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (q p : SymbolicTrace J) (hQ : SymbolicAt A q) (hP : SymbolicAt A p) :
    F.toFun (refinesValue site (decodeSymbolicTrace site H q) (decodeSymbolicTrace site H p)) =
      refinesValue site' (decodeSymbolicTrace site' H' q) (decodeSymbolicTrace site' H' p) := by
  have hq := decodeSymbolicTrace_completeMap_on_log F q site H site' H'
    (fun i hi => hS i (hQ i hi)) (fun i hi => hH i (hQ i hi))
  have hp := decodeSymbolicTrace_completeMap_on_log F p site H site' H'
    (fun i hi => hS i (hP i hi)) (fun i hi => hH i (hP i hi))
  rw [map_refinesValue,hq,hp]
  unfold refinesValue
  rw [agreementValue_eq_on_pins _ _ _ site' (fun i hi =>
    hS i (allowed_of_decode_pin site' H' p hP hi))]

def SymbolicLabelAt (A : J → Prop) : Option (SymbolicTrace J) → Prop
  | none => True
  | some p => SymbolicAt A p

abbrev SupportedSymbolic (J : Type) (A : J → Prop) := {p : Option (SymbolicTrace J) // SymbolicLabelAt A p}

noncomputable def supportedSymbolicQ (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (A : J → Prop) : ValuedPoset B (SupportedSymbolic J A) where
  valid n := (symbolicPolynomialQ site H).valid n.val
  refines n p := (symbolicPolynomialQ site H).refines n.val p.val
  refine_valid n p := (symbolicPolynomialQ site H).refine_valid _ _
  refl n := (symbolicPolynomialQ site H).refl _
  trans n q p := (symbolicPolynomialQ site H).trans _ _ _
  weakest := ⟨none,True.intro⟩
  weakest_valid := rfl
  weaker n := (symbolicPolynomialQ site H).weaker _

theorem symbolicLabel_partial_map {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (p : Option (SymbolicTrace J)) (hP : SymbolicLabelAt A p) :
    F.toFun ((symbolicPolynomialQ site H).valid p) =
      (symbolicPolynomialQ site' H').valid p := by
  cases p with
  | none => exact F.map_top
  | some p => exact symbolicPolyValid_partial_map F site H site' H' hS hH p hP

theorem symbolicLabel_refines_partial_map {A : J → Prop} (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (q p : Option (SymbolicTrace J)) (hQ : SymbolicLabelAt A q) (hP : SymbolicLabelAt A p) :
    F.toFun ((symbolicPolynomialQ site H).refines q p) =
      (symbolicPolynomialQ site' H').refines q p := by
  cases q with
  | none =>
    cases p with
    | none => exact F.map_top
    | some p => exact F.map_bot
  | some q =>
    cases p with
    | none => exact symbolicPolyValid_partial_map F site H site' H' hS hH q hQ
    | some p =>
      change F.toFun ((polyValid site H (decodeSymbolicTrace site H q) ⊓
        polyValid site H (decodeSymbolicTrace site H p)) ⊓
        refinesValue site (decodeSymbolicTrace site H q) (decodeSymbolicTrace site H p)) = _
      simp only [F.map_inf,symbolicPolyValid_partial_map F site H site' H' hS hH q hQ,
        symbolicPolyValid_partial_map F site H site' H' hS hH p hP,
        symbolicRefines_partial_map F site H site' H' hS hH q p hQ hP]
      <;> rfl

end JSP000930.Negative
