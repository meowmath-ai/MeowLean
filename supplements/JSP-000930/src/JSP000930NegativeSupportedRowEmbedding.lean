import JSP000930NegativeSupportedLogEvaluation
import JSP000930FixedTaggedStageForcing
import JSP000930NegativeActualFineTower

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion
  JSP000933.ForcingTransport JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] {A : J → Prop}

private theorem raise_iInf930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) (f : J → B) :
    (⨅ j : {j // j ∈ (highDecode930 site H p).pins},f j.val) =
      ⨅ i : {i // i ∈ (lowDecode930 site H p).pins},f i.val.val := by
  apply le_antisymm
  · exact le_iInf fun i => iInf_le (fun j : {j // j ∈ (highDecode930 site H p).pins} => f j.val) ⟨i.val.val,(raise_decode_pin_iff930 site H p i.val).mpr i.property⟩
  · apply le_iInf
    intro j
    obtain ⟨i,hi,he⟩ := (raise_decode_mem930 site H p j.val).mp j.property
    exact (iInf_le (fun x : {i // i ∈ (lowDecode930 site H p).pins} => f x.val.val) ⟨i,hi⟩).trans_eq
      (congrArg f he)

theorem raise_polyValid930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) :
    polyValid site H (highDecode930 site H p) =
      polyValid (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H) (lowDecode930 site H p) := by
  unfold polyValid paletteValue
  rw [raise_decode_coeff930 site H p]
  simp only [raise_eval930]
  apply congrArg (fun x : B => coeffValue (lowDecode930 site H p).coeff ⊓ x)
  exact raise_iInf930 site H p (fun j => ⨆ n : ℕ, ((lowDecode930 site H p).eval (site j)).name =ᴮ (H j n).name)

private theorem raise_subset930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p q : SymbolicTrace (AllowedPin A)) :
    (highDecode930 site H p).pins ⊆ (highDecode930 site H q).pins ↔
      (lowDecode930 site H p).pins ⊆ (lowDecode930 site H q).pins := by
  constructor
  · intro h i hi
    exact (raise_decode_pin_iff930 site H q i).mp (h ((raise_decode_pin_iff930 site H p i).mpr hi))
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := (raise_decode_mem930 site H p j).mp hj
    exact (raise_decode_pin_iff930 site H q i).mpr (h hi)

theorem raise_refinesValue930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (q p : SymbolicTrace (AllowedPin A)) :
    refinesValue site (highDecode930 site H q) (highDecode930 site H p) =
      refinesValue (allowedSite930 (A := A) site) (lowDecode930 site H q) (lowDecode930 site H p) := by
  have ha : agreementValue site (highDecode930 site H q) (highDecode930 site H p) =
      agreementValue (allowedSite930 (A := A) site) (lowDecode930 site H q) (lowDecode930 site H p) := by
    unfold agreementValue
    simp only [raise_eval930]
    exact raise_iInf930 site H p (fun j =>
      ((lowDecode930 site H q).eval (site j)).name =ᴮ ((lowDecode930 site H p).eval (site j)).name)
  have hg : discValue (highDecode930 site H q) (highDecode930 site H p) =
      discValue (lowDecode930 site H q) (lowDecode930 site H p) := by
    unfold discValue
    apply iInf_congr
    intro g
    simp only [raise_eval930]
    rfl
  unfold refinesValue
  rw [ha,hg,propext (raise_subset930 site H p q)] <;> rfl

theorem supportedLabelChart930_valid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : Option (SymbolicTrace (AllowedPin A))) :
    (supportedSymbolicQ site H A).valid (supportedLabelChart930 p) =
      (symbolicPolynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)).valid p := by
  cases p with
  | none => rfl
  | some p => exact raise_polyValid930 site H p

theorem supportedLabelChart930_refines (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p q : Option (SymbolicTrace (AllowedPin A))) :
    (supportedSymbolicQ site H A).refines (supportedLabelChart930 p) (supportedLabelChart930 q) =
      (symbolicPolynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)).refines p q := by
  cases p with
  | none => cases q <;> rfl
  | some p =>
    cases q with
    | none => exact raise_polyValid930 site H p
    | some q =>
      change (polyValid site H (highDecode930 site H p) ⊓ polyValid site H (highDecode930 site H q)) ⊓
        refinesValue site (highDecode930 site H p) (highDecode930 site H q) =
        (polyValid (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H) (lowDecode930 site H p) ⊓
         polyValid (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H) (lowDecode930 site H q)) ⊓
        refinesValue (allowedSite930 (A := A) site) (lowDecode930 site H p) (lowDecode930 site H q)
      rw [raise_polyValid930,raise_polyValid930,raise_refinesValue930]

noncomputable def supportedTotalChart930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) :
    TotalCondition (symbolicPolynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)) ≃o
      TotalCondition (supportedSymbolicQ site H A) where
  toFun p := ⟨p.mask,supportedLabelChart930 p.trace,p.nonzero,by
    rw [supportedLabelChart930_valid]; exact p.valid⟩
  invFun p := ⟨p.mask,supportedLabelChart930.symm p.trace,p.nonzero,by
    rw [← supportedLabelChart930_valid,supportedLabelChart930.apply_symm_apply]; exact p.valid⟩
  left_inv p := by
    refine totalCondition_eq_of_data _ p ?_ ?_
    · rfl
    exact supportedLabelChart930.symm_apply_apply p.trace
  right_inv p := by
    refine totalCondition_eq_of_data _ p ?_ ?_
    · rfl
    exact supportedLabelChart930.apply_symm_apply p.trace
  map_rel_iff' := by
    intro p q
    change (p.mask ≤ q.mask ∧ p.mask ≤
      (supportedSymbolicQ site H A).refines (supportedLabelChart930 p.trace) (supportedLabelChart930 q.trace)) ↔ _
    rw [supportedLabelChart930_refines] <;> rfl

noncomputable def supportedRawDense930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hS : ∀ i : AllowedPin A,(site i.val).CutOn (⊤ : B))
    (hH : ∀ (i : AllowedPin A) n,(H i.val n).CutOn (⊤ : B))
    (hA : ∀ i j : AllowedPin A,i≠j → (⊤ : B) ≤ ((site i.val).name =ᴮ (site j.val).name)ᶜ) :
    DenseForcingMap (TotalCondition (supportedSymbolicQ site H A))
      (TotalCondition (polynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H))) :=
  denseForcingMap_comp930
    (denseForcingMapOfIso930 (supportedTotalChart930 (A := A) site H).symm)
    (symbolicDenseForcingMap (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H) hS hH hA)

theorem supportedRawDense930_base (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hS : ∀ i : AllowedPin A,(site i.val).CutOn (⊤ : B))
    (hH : ∀ (i : AllowedPin A) n,(H i.val n).CutOn (⊤ : B))
    (hA : ∀ i j : AllowedPin A,i≠j → (⊤ : B) ≤ ((site i.val).name =ᴮ (site j.val).name)ᶜ)
    (b : B) :
    (supportedRawDense930 site H hS hH hA).pullIso
      (baseEmbed (polynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)) b) =
      baseEmbed (supportedSymbolicQ site H A) b := by
  unfold supportedRawDense930
  rw [densePull_comp930,symbolicDenseForcingMap_base]
  let D := denseForcingMapOfIso930 (supportedTotalChart930 (A := A) site H).symm
  let Q := symbolicPolynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)
  let R := supportedSymbolicQ site H A
  have ht (p : TotalCondition R) :
      imageCondition p ≤ D.pullIso (baseEmbed Q b) ↔ imageCondition p ≤ baseEmbed R b := by
    calc
      imageCondition p ≤ D.pullIso (baseEmbed Q b) ↔ D.map p ∈ (baseEmbed Q b : LowerSet _) :=
        image_le_iff_member p _
      _ ↔ imageCondition (D.map p) ≤ baseEmbed Q b := (image_le_iff_member (D.map p) _).symm
      _ ↔ p.mask ≤ b := baseEmbed_reflects_mask_r427 (D.map p) b
      _ ↔ imageCondition p ≤ baseEmbed R b := (baseEmbed_reflects_mask_r427 p b).symm
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp)) (le_of_image_tests (fun p => (ht p).mpr))

noncomputable def supportedRawToSymbolic930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hS : ∀ i : AllowedPin A,(site i.val).CutOn (⊤ : B))
    (hH : ∀ (i : AllowedPin A) n,(H i.val n).CutOn (⊤ : B))
    (hA : ∀ i j : AllowedPin A,i≠j → (⊤ : B) ≤ ((site i.val).name =ᴮ (site j.val).name)ᶜ) :
    CompleteValueMap (TotalBA (polynomialQ (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)))
      (TotalBA (supportedSymbolicQ site H A)) :=
  completeMapOfDensePull930 (supportedRawDense930 site H hS hH hA)

theorem supportedRawToSymbolic930_base (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hS : ∀ i : AllowedPin A,(site i.val).CutOn (⊤ : B))
    (hH : ∀ (i : AllowedPin A) n,(H i.val n).CutOn (⊤ : B))
    (hA : ∀ i j : AllowedPin A,i≠j → (⊤ : B) ≤ ((site i.val).name =ᴮ (site j.val).name)ᶜ)
    (b : B) :
    (supportedRawToSymbolic930 site H hS hH hA).toFun
      ((polynomialBaseValueMap (allowedSite930 (A := A) site) (allowedPalette930 (A := A) H)).toFun b) =
      baseEmbed (supportedSymbolicQ site H A) b :=
  supportedRawDense930_base site H hS hH hA b

end JSP000930.Negative
