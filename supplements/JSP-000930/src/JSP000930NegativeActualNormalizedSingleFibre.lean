import JSP000930NegativeWeightedDenseLabelEquivalence
import JSP000930SymbolicTraceDensity
import JSP000930SymbolicSupportedForcing

open Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def supportedDecodeLabel
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop)
    (p : SupportedSymbolic J A) : SupportedNamedRow B J A := by
  rcases p with ⟨_ | p,hp⟩
  · exact ⟨none,by simp [NamedRowAt,polyLabelPins]⟩
  · exact ⟨some (decodeSymbolicTrace site H p),fun _ h => allowed_of_decode_pin site H p hp h⟩

noncomputable def supportedWeightedDecode
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop)
    (hSite : ∀ i,A i → (site i).CutOn (⊤ : B))
    (hH : ∀ i,A i → ∀ n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j,A i → A j → i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ) :
    WeightedDenseLabels (supportedSymbolicQ site H A) (supportedNamedRowQ site H A) where
  label := supportedDecodeLabel site H A
  valid := by intro p; rcases p with ⟨_ | _,_⟩ <;> rfl
  refines := by
    intro p q
    rcases p with ⟨_ | _,_⟩ <;> rcases q with ⟨_ | _,_⟩ <;> rfl
  dense := by
    intro p m hm hv
    rcases p with ⟨_ | p,hp⟩
    · exact ⟨⟨none,True.intro⟩,m,hm,le_rfl,le_top⟩
    · obtain ⟨s,t,hs,hsm,hpins,href⟩ := exists_symbolic_refinement_on_pins site H p
        (fun i hi => hSite i (hp i hi))
        (fun i hi => hH i (hp i hi))
        (fun i hi j hj hn => hApart i j (hp i hi) (hp j hj) hn) m hm hv
      have ht : SymbolicAt A t := (decodeSymbolicTrace_support_iff site H t).mp
        (fun i hi => hp i (show i ∈ p.pins from hpins ▸ hi))
      exact ⟨⟨some t,ht⟩,s,hs,hsm,href⟩

theorem supportedSymbolic_one_fibre_relativeCCC
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC (supportedSymbolicQ site H A)) :
    ForcesRelativeCCC (supportedSymbolicQ site H (fun j => A j ∨ j = z)) := by
  let E₀ := supportedWeightedDecode site H A
    (fun i _ => hSite i) (fun i _ => hH i) (fun i j hi hj => hApart i j (Or.inl hi) (Or.inl hj))
  let E₁ := supportedWeightedDecode site H (fun j => A j ∨ j = z)
    (fun i _ => hSite i) (fun i _ => hH i) hApart
  exact (E₁.relativeCCC_iff hB).mpr
    ((namedRow_spliceCondensation site H A z hSite hApart).relativeCCC hB
      ((E₀.relativeCCC_iff hB).mp hOld))

end JSP000930.Negative
