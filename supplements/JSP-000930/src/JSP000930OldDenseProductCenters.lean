import JSP000930MarkedAnalyticRowProduct

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 650000 in
theorem simultaneously_normalize_old_centers [Fintype I] {A : J → Prop}
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (hSite : ∀ j,A j → (site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j → ∀ k,A k → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (p : I → PolyTrace B J) (hP : ∀ i j,j ∈ (p i).pins → A j)
    (m : B) (hm : m ≠ ⊥) (hV : ∀ i,m ≤ polyValid site (H i) (p i)) :
    ∃ (s : B) (u : I → SupportedSymbolic J A),s ≠ ⊥ ∧ s ≤ m ∧
      ∀ i,s ≤ (polynomialQ site (H i)).refines
        ((u i).val.map (decodeSymbolicTrace site (H i))) (some (p i)) := by
  classical
  have hFinite (K : Finset I) (b : B) (hb : b ≠ ⊥)
      (hK : ∀ i ∈ K,b ≤ polyValid site (H i) (p i)) :
      ∃ (s : B) (u : I → SupportedSymbolic J A),s ≠ ⊥ ∧ s ≤ b ∧
        ∀ i ∈ K,s ≤ (polynomialQ site (H i)).refines
          ((u i).val.map (decodeSymbolicTrace site (H i))) (some (p i)) := by
    induction K using Finset.induction_on generalizing b with
    | empty =>
      refine ⟨b,fun _ => ⟨none,True.intro⟩,hb,le_rfl,?_⟩
      intro i hi
      simp at hi
    | @insert i K hi ih =>
      obtain ⟨a,t,ha,haB,hPins,hRef⟩ := exists_symbolic_refinement_on_pins site (H i) (p i)
        (fun j hj => hSite _ (hP i j hj)) (fun j hj n => hH i j (hP i j hj) n)
        (fun j hj k hk hn => hApart _ (hP i j hj) _ (hP i k hk) hn)
        b hb (hK i (Finset.mem_insert_self i K))
      have hT : SymbolicAt A t := (decodeSymbolicTrace_support_iff site (H i) t).mp (by
        rw [hPins]
        exact hP i)
      obtain ⟨s,u,hs,hsA,hRest⟩ := ih a ha (fun j hj =>
        haB.trans (hK j (Finset.mem_insert_of_mem hj)))
      let v (j : I) : SupportedSymbolic J A := if j = i then ⟨some t,hT⟩ else u j
      refine ⟨s,v,hs,hsA.trans haB,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · simpa [v] using hsA.trans hRef
      · have hne : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [v,ite_eq_right hne] using hRest j hj
  obtain ⟨s,u,hs,hsM,hR⟩ := hFinite Finset.univ m hm (fun i _ => hV i)
  exact ⟨s,u,hs,hsM,fun i => hR i (Finset.mem_univ i)⟩

set_option maxHeartbeats 450000 in
theorem old_dense_product_refines_actual_centers [Fintype I] {A : J → Prop}
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (hSite : ∀ j,A j → (site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j → ∀ k,A k → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (E : Set (TotalCondition (rowProductQ (fun i => supportedSymbolicQ site (H i) A))))
    (hE : DenseConditionSet E)
    (p : I → PolyTrace B J) (hP : ∀ i j,j ∈ (p i).pins → A j)
    (m : B) (hm : m ≠ ⊥) (hV : ∀ i,m ≤ polyValid site (H i) (p i)) :
    ∃ d : TotalCondition (rowProductQ (fun i => supportedSymbolicQ site (H i) A)),
      d ∈ E ∧ d.mask ≤ m ∧
      ∀ i, ∃ t : SymbolicTrace J,(d.trace i).val = some t ∧
        d.mask ≤ (polynomialQ site (H i)).refines (some (decodeSymbolicTrace site (H i) t))
          (some (p i)) := by
  let Q (i : I) := supportedSymbolicQ site (H i) A
  let V := rowProductQ Q
  obtain ⟨s,u,hs,hsM,hR⟩ := simultaneously_normalize_old_centers site H hSite hH hApart p hP m hm hV
  let w : TotalCondition V := ⟨s,u,hs,le_iInf (fun i =>
    ((hR i).trans ((polynomialQ site (H i)).refine_valid _ _)).trans inf_le_left)⟩
  obtain ⟨d,hd,hDE⟩ := hE w
  have hD : d.mask ≤ s := hd.1
  refine ⟨d,hDE,hD.trans hsM,?_⟩
  intro i
  have hDi := (le_product_refines_iff Q _ _ _).mp hd.2 i
  have hh : d.mask ≤ (polynomialQ site (H i)).refines
      ((d.trace i).val.map (decodeSymbolicTrace site (H i)))
      ((u i).val.map (decodeSymbolicTrace site (H i))) := hDi
  have h := (le_inf hh (hD.trans (hR i))).trans ((polynomialQ site (H i)).trans _ _ _)
  cases he : (d.trace i).val with
  | none =>
    rw [he] at h
    exact (d.nonzero (le_bot_iff.mp h)).elim
  | some t =>
    refine ⟨t,rfl,?_⟩
    rw [he] at h
    exact h

end JSP000930.Negative
