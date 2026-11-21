import JSP000930NegativeActualNormalizedSingleFibre

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B N M T J I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def WeightedDenseLabels.withUnchangedRows
    {Q : ValuedPoset B N} {P : ValuedPoset B M} (F : WeightedDenseLabels Q P)
    (R : ValuedPoset B T) : WeightedDenseLabels (pairedRowQ Q R) (pairedRowQ P R) where
  label p := (F.label p.1,p.2)
  valid p := congrArg (fun x => x ⊓ R.valid p.2) (F.valid p.1)
  refines p q := congrArg (fun x => x ⊓ R.refines p.2 q.2) (F.refines p.1 q.1)
  dense := by
    intro p m hm hV
    obtain ⟨a,s,hs,hsm,hA⟩ := F.dense p.1 m hm (hV.trans inf_le_left)
    exact ⟨(a,p.2),s,hs,hsm,le_inf hA
      (hsm.trans ((hV.trans inf_le_right).trans (R.refl p.2)))⟩

theorem supportedSymbolic_one_fibre_product_relativeCCC
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (R : ValuedPoset B T) (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC (pairedRowQ (supportedSymbolicQ site H A) R)) :
    ForcesRelativeCCC (pairedRowQ (supportedSymbolicQ site H (fun j => A j ∨ j = z)) R) := by
  let E₀ := (supportedWeightedDecode site H A
    (fun i _ => hSite i) (fun i _ => hH i)
    (fun i j hi hj => hApart i j (Or.inl hi) (Or.inl hj))).withUnchangedRows R
  let E₁ := (supportedWeightedDecode site H (fun j => A j ∨ j = z)
    (fun i _ => hSite i) (fun i _ => hH i) hApart).withUnchangedRows R
  exact (E₁.relativeCCC_iff hB).mpr
    (((namedRow_spliceCondensation site H A z hSite hApart).withUnchangedRows R).relativeCCC hB
      ((E₀.relativeCCC_iff hB).mp hOld))

theorem supportedSymbolic_one_fibre_rowProduct_relativeCCC
    {Ns : I → Type} (rows : ∀ i,ValuedPoset B (Ns i))
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC (pairedRowQ (supportedSymbolicQ site H A) (rowProductQ rows))) :
    ForcesRelativeCCC (pairedRowQ (supportedSymbolicQ site H (fun j => A j ∨ j = z))
      (rowProductQ rows)) :=
  supportedSymbolic_one_fibre_product_relativeCCC site H A z (rowProductQ rows)
    hB hSite hH hApart hOld

end JSP000930.Negative
