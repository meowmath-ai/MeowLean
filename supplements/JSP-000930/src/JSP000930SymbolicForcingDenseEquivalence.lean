import JSP000930SymbolicTraceDensity
import JSP000933DenseForcingMap
import JSP000933MarkedNameTransport

open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion
open JSP000933.ForcingTransport

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def symbolicPolynomialQ (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) :
    ValuedPoset B (Option (SymbolicTrace J)) where
  valid n := (polynomialQ site H).valid (n.map (decodeSymbolicTrace site H))
  refines n p := (polynomialQ site H).refines (n.map (decodeSymbolicTrace site H))
    (p.map (decodeSymbolicTrace site H))
  refine_valid n p := (polynomialQ site H).refine_valid _ _
  refl n := (polynomialQ site H).refl _
  trans n q p := (polynomialQ site H).trans _ _ _
  weakest := none
  weakest_valid := (polynomialQ site H).weakest_valid
  weaker n := (polynomialQ site H).weaker _

noncomputable def decodeSymbolicCondition (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : TotalCondition (symbolicPolynomialQ site H)) :
    TotalCondition (polynomialQ site H) :=
  ⟨p.mask,p.trace.map (decodeSymbolicTrace site H),p.nonzero,p.valid⟩

theorem decodeSymbolicCondition_le_iff (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p q : TotalCondition (symbolicPolynomialQ site H)) :
    decodeSymbolicCondition site H p ≤ decodeSymbolicCondition site H q ↔ p ≤ q :=
  Iff.rfl

theorem decodeSymbolicCondition_dense (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B)) (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j : J,i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (p : TotalCondition (polynomialQ site H)) :
    ∃ q : TotalCondition (symbolicPolynomialQ site H), decodeSymbolicCondition site H q ≤ p := by
  cases he : p.trace with
  | none =>
    let q : TotalCondition (symbolicPolynomialQ site H) :=
      ⟨p.mask,none,p.nonzero,le_top⟩
    refine ⟨q,le_rfl,?_⟩
    change p.mask ≤ (polynomialQ site H).refines none p.trace
    rw [he]
    exact le_top
  | some t =>
    have hV : p.mask ≤ polyValid site H t := by
      have h := p.valid
      rw [he] at h
      exact h
    obtain ⟨k,s,hk,hkP,hPins,hRef⟩ :=
      exists_symbolic_refinement site H hSite hH hApart t p.mask p.nonzero hV
    let q : TotalCondition (symbolicPolynomialQ site H) :=
      ⟨k,some s,hk,(hRef.trans ((polynomialQ site H).refine_valid _ _)).trans inf_le_left⟩
    refine ⟨q,hkP,?_⟩
    change k ≤ (polynomialQ site H).refines (some (decodeSymbolicTrace site H s)) p.trace
    rw [he]
    exact hRef

noncomputable def symbolicDenseForcingMap (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B)) (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j : J,i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ) :
    DenseForcingMap (TotalCondition (symbolicPolynomialQ site H)) (TotalCondition (polynomialQ site H))
    where
  map := decodeSymbolicCondition site H
  monotone := by
    intro p q h
    exact (decodeSymbolicCondition_le_iff site H p q).mpr h
  dense := decodeSymbolicCondition_dense site H hSite hH hApart
  reflect_compatible := by
    intro p q h
    obtain ⟨t,htP,htQ⟩ := h
    obtain ⟨s,hs⟩ := decodeSymbolicCondition_dense site H hSite hH hApart t
    exact ⟨s,(decodeSymbolicCondition_le_iff site H _ _).mp (hs.trans htP),
      (decodeSymbolicCondition_le_iff site H _ _).mp (hs.trans htQ)⟩

theorem symbolicDenseForcingMap_base (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B)) (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j : J,i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ) (b : B) :
    (symbolicDenseForcingMap site H hSite hH hApart).pullIso (baseEmbed (polynomialQ site H) b) =
      baseEmbed (symbolicPolynomialQ site H) b := by
  let D := symbolicDenseForcingMap site H hSite hH hApart
  change D.pullIso (baseEmbed (polynomialQ site H) b) = baseEmbed (symbolicPolynomialQ site H) b
  have ht (p : TotalCondition (symbolicPolynomialQ site H)) :
      imageCondition p ≤ D.pullIso (baseEmbed (polynomialQ site H) b) ↔
        imageCondition p ≤ baseEmbed (symbolicPolynomialQ site H) b := by
    rw [image_le_iff_member]
    change D.map p ∈ (baseEmbed (polynomialQ site H) b : LowerSet _) ↔ _
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427,baseEmbed_reflects_mask_r427] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
    (le_of_image_tests (fun p => (ht p).mpr))

end JSP000930.Negative
