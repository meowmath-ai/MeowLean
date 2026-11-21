import JSP000930NegativeNormalizedOneFibreRowProduct

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000930.BooleanAnalysis

variable {B I N J : Type} [NontrivialCompleteBooleanAlgebra B] {Ns : I → Type}

abbrev PointedRows (N : Type) (Ns : I → Type) : Unit ⊕ I → Type
  | .inl _ => N
  | .inr i => Ns i

def pointedRowFamily (Q : ValuedPoset B N) (R : ∀ i,ValuedPoset B (Ns i)) :
    ∀ i,ValuedPoset B (PointedRows N Ns i)
  | .inl _ => Q
  | .inr i => R i

def packPointedRows (p : N × (∀ i,Ns i)) : ∀ i,PointedRows N Ns i
  | .inl _ => p.1
  | .inr i => p.2 i

theorem iInf_pointed_rows (f : Unit ⊕ I → B) :
    (⨅ i,f i) = f (.inl ()) ⊓ (⨅ i,f (.inr i)) := by
  apply le_antisymm
  · exact le_inf (iInf_le f (.inl ())) (le_iInf fun i => iInf_le f (.inr i))
  · apply le_iInf
    intro i
    rcases i with ⟨⟩ | i
    · exact inf_le_left
    · exact inf_le_right.trans (iInf_le (fun j : I => f (.inr j)) i)

noncomputable def pointedRowProduct_pack
    (Q : ValuedPoset B N) (R : ∀ i,ValuedPoset B (Ns i)) :
    WeightedDenseLabels (pairedRowQ Q (rowProductQ R)) (rowProductQ (pointedRowFamily Q R)) where
  label := packPointedRows
  valid p := iInf_pointed_rows (fun i => (pointedRowFamily Q R i).valid (packPointedRows p i))
  refines p q := iInf_pointed_rows (fun i => (pointedRowFamily Q R i).refines
    (packPointedRows p i) (packPointedRows q i))
  dense := by
    intro p m hm hV
    let u : N × (∀ i,Ns i) := (p (.inl ()),fun i => p (.inr i))
    have he : packPointedRows u = p := by
      funext i
      rcases i with ⟨⟩ | i <;> rfl
    refine ⟨u,m,hm,le_rfl,?_⟩
    rw [he]
    exact hV.trans ((rowProductQ (pointedRowFamily Q R)).refl p)

theorem supportedSymbolic_one_fibre_nativeRowProduct_relativeCCC
    (R : ∀ i,ValuedPoset B (Ns i))
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC
      (rowProductQ (pointedRowFamily (supportedSymbolicQ site H A) R))) :
    ForcesRelativeCCC
      (rowProductQ (pointedRowFamily (supportedSymbolicQ site H (fun j => A j ∨ j = z)) R)) := by
  apply ((pointedRowProduct_pack _ R).relativeCCC_iff hB).mp
  exact supportedSymbolic_one_fibre_rowProduct_relativeCCC R site H A z hB hSite hH hApart
    (((pointedRowProduct_pack _ R).relativeCCC_iff hB).mpr hOld)

end JSP000930.Negative
