import JSP000930SymbolicTrimCommonRefinement

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem supportedSymbolic_decoded_pins {A : J → Prop}
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SupportedSymbolic J A) :
    ∀ i ∈ polyLabelPins (p.val.map (decodeSymbolicTrace site H)),A i := by
  rcases p with ⟨p,hp⟩
  cases p with
  | none =>
    intro i hi
    change i ∈ (∅ : Finset J) at hi
    simp at hi
  | some p =>
    exact (decodeSymbolicTrace_support_iff site H p).mpr hp

theorem symbolic_common_on_old_support {A : J → Prop}
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,A i → (site i).CutOn (⊤ : B))
    (hH : ∀ i,A i → ∀ n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i,A i → ∀ j,A j → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (p q : SupportedSymbolic J A) (v : Option (PolyTrace B J))
    (m : B) (hm : m ≠ ⊥)
    (hp : m ≤ (polynomialQ site H).refines v (p.val.map (decodeSymbolicTrace site H)))
    (hq : m ≤ (polynomialQ site H).refines v (q.val.map (decodeSymbolicTrace site H))) :
    ∃ (s : B) (u : SupportedSymbolic J A), s ≠ ⊥ ∧ s ≤ m ∧
      s ≤ (supportedSymbolicQ site H A).refines u p ∧
      s ≤ (supportedSymbolicQ site H A).refines u q := by
  classical
  cases v with
  | none => exact ⟨m,⟨none,True.intro⟩,hm,le_rfl,hp,hq⟩
  | some v =>
    let P := p.val.map (decodeSymbolicTrace site H)
    let Q := q.val.map (decodeSymbolicTrace site H)
    let l := polyLabelPins P ∪ polyLabelPins Q
    have hpL : polyLabelPins P ⊆ l := Finset.subset_union_left
    have hqL : polyLabelPins Q ⊆ l := Finset.subset_union_right
    have hLV : l ⊆ v.pins := Finset.union_subset
      (polyLabelPins_subset_of_refines site H v P m hm hp)
      (polyLabelPins_subset_of_refines site H v Q m hm hq)
    have hA (i : J) (hi : i ∈ l) : A i := by
      rcases Finset.mem_union.mp hi with hi | hi
      · exact supportedSymbolic_decoded_pins site H p i hi
      · exact supportedSymbolic_decoded_pins site H q i hi
    let w := v.trimPins l
    have hwp := trim_refines_polyLabel site H v P m hm hp l hpL hLV
    have hwq := trim_refines_polyLabel site H v Q m hm hq l hqL hLV
    have hw : m ≤ polyValid site H w :=
      hwp.trans (((polynomialQ site H).refine_valid _ _).trans inf_le_left)
    obtain ⟨s,u,hs,hsM,hPins,hRef⟩ := exists_symbolic_refinement_on_pins site H w
      (fun i hi => hSite i (hA i hi)) (fun i hi n => hH i (hA i hi) n)
      (fun i hi j hj hn => hApart i (hA i hi) j (hA j hj) hn) m hm hw
    have hU : SymbolicAt A u := (decodeSymbolicTrace_support_iff site H u).mp (by
      rw [hPins]
      exact hA)
    refine ⟨s,⟨some u,hU⟩,hs,hsM,?_ ,?_⟩
    · exact (le_inf hRef (hsM.trans hwp)).trans ((polynomialQ site H).trans _ _ _)
    · exact (le_inf hRef (hsM.trans hwq)).trans ((polynomialQ site H).trans _ _ _)

end JSP000930.Negative
