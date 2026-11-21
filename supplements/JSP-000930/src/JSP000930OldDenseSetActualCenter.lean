import JSP000930CohenRetargetEarlierValue

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem old_dense_set_refines_actual_center {A : J → Prop}
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,A i → (site i).CutOn (⊤ : B))
    (hH : ∀ i,A i → ∀ n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i,A i → ∀ j,A j → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (E : Set (TotalCondition (supportedSymbolicQ site H A))) (hE : DenseConditionSet E)
    (p : PolyTrace B J) (hP : ∀ i ∈ p.pins,A i)
    (m : B) (hm : m ≠ ⊥) (hV : m ≤ polyValid site H p) :
    ∃ d : TotalCondition (supportedSymbolicQ site H A),d ∈ E ∧ d.mask ≤ m ∧
      ∃ t : SymbolicTrace J,d.trace.val = some t ∧
        d.mask ≤ (polynomialQ site H).refines (some (decodeSymbolicTrace site H t)) (some p) := by
  obtain ⟨s,t,hs,hsM,hPins,hRef⟩ := exists_symbolic_refinement_on_pins site H p
    (fun i hi => hSite i (hP i hi)) (fun i hi n => hH i (hP i hi) n)
    (fun i hi j hj hn => hApart i (hP i hi) j (hP j hj) hn) m hm hV
  have hA : SymbolicAt A t := (decodeSymbolicTrace_support_iff site H t).mp (by
    rw [hPins]
    exact hP)
  let Q := supportedSymbolicQ site H A
  let c : TotalCondition Q := ⟨s,⟨some t,hA⟩,hs,
    (hRef.trans ((polynomialQ site H).refine_valid _ _)).trans inf_le_left⟩
  obtain ⟨d,hd,hDE⟩ := hE c
  have hD : d.mask ≤ s := hd.1
  have hh : d.mask ≤ (polynomialQ site H).refines
      (d.trace.val.map (decodeSymbolicTrace site H)) (some (decodeSymbolicTrace site H t)) := hd.2
  refine ⟨d,hDE,hD.trans hsM,?_⟩
  cases hT : d.trace.val with
  | none =>
    rw [hT] at hh
    exact (d.nonzero (le_bot_iff.mp hh)).elim
  | some u =>
    refine ⟨u,rfl,?_⟩
    rw [hT] at hh
    exact (le_inf hh (hD.trans hRef)).trans ((polynomialQ site H).trans _ _ _)

end JSP000930.Negative
