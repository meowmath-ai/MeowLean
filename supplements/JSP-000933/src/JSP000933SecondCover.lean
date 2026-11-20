import JSP000933ExactLift

open Filter
open scoped Topology

namespace JSP000933

noncomputable section

def OpenColoringPrinciple : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T3Space T],
    ∀ K : Set (T × T), IsOpen K →
      (∀ p q : T, (p,q) ∈ K → (q,p) ∈ K) → (∀ p : T, (p,p) ∉ K) →
      (∃ C : Set T, ¬ C.Countable ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q → (p,q) ∈ K) ∨
        (∃ V : ℕ → Set T, (⋃ n, V n) = Set.univ ∧
          ∀ n p, p ∈ V n → ∀ q, q ∈ V n → p ≠ q → (p,q) ∉ K)

theorem exists_secondColor_cover_and_samples
    [TopologicalSpace Bool] [DiscreteTopology Bool] [SecondCountableTopology Bool] [T3Space Bool]
    (hOCA : OpenColoringPrinciple) {A : Set (Set ℕ)} (F : Set ℕ → Set ℕ)
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e)
    (g : EUWeight) {ε : ℝ} (hε : 0 < ε)
    (hMeet : ∀ X Y : Set ℕ, WeightedNull g.weight (xorSet (F X ∩ F Y) (F (X ∩ Y)))) :
    ∃ (V D : ℕ → Set (CrossPoint A F)), (⋃ n, V n) = Set.univ ∧
      (∀ n p, p ∈ V n → ∀ q, q ∈ V n → (p,q) ∉ crossingColor e g ε) ∧
      ∀ n, (D n).Countable ∧ D n ⊆ V n ∧ V n ⊆ closure (D n) := by
  classical
  let K : Set (CrossPoint A F × CrossPoint A F) := crossingColor e g ε
  have hO : IsOpen K := isOpen_crossingColor hA g ε
  have hsym (p q : CrossPoint A F) : (p,q) ∈ K → (q,p) ∈ K :=
    crossingColor_symmetric e g ε
  have hir (p : CrossPoint A F) : (p,p) ∉ K :=
    crossingColor_irreflexive hA g ε p
  rcases hOCA (CrossPoint A F) K hO hsym hir with hfirst | hsecond
  · obtain ⟨C,hcount,hC⟩ := hfirst
    exact False.elim (hcount (crossingColor_countable_clique e g hε hMeet hC))
  · obtain ⟨V,hV,hCompl⟩ := hsecond
    have hs (n : ℕ) : ∃ t : Set (CrossPoint A F), t.Countable ∧ t ⊆ V n ∧ V n ⊆ closure t :=
      TopologicalSpace.exists_countable_dense_subset (V n)
    choose D hD using hs
    refine ⟨V,D,hV,?_,hD⟩
    intro n p hp q hq
    by_cases he : p = q
    · subst q
      exact hir p
    · exact hCompl n p hp q hq he

private theorem capOf_has_family_support_r17 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (p : CrossPoint A F) : ∃ a ∈ A, capOf p ⊆ a := p.2.2.2.1

theorem exists_family_domain_away_all_samples
    {A : Set (Set ℕ)} (hA : ¬ A.Countable)
    (hAD : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite)
    {F : Set ℕ → Set ℕ} (D : ℕ → ℕ → Set (CrossPoint A F))
    (hD : ∀ j n, (D j n).Countable) :
    ∃ c ∈ A, ∀ j n, ∀ p ∈ D j n, (capOf p ∩ c).Finite := by
  classical
  choose a haSpec using (fun p : CrossPoint A F => capOf_has_family_support_r17 p)
  have ha (p : CrossPoint A F) := (haSpec p).1
  have hsub (p : CrossPoint A F) := (haSpec p).2
  let S : Set (CrossPoint A F) := ⋃ j : ℕ, ⋃ n : ℕ, D j n
  have hs : S.Countable := Set.countable_iUnion (fun j => Set.countable_iUnion (hD j))
  have hi : (a '' S).Countable := hs.image a
  have hnot : ¬ A ⊆ a '' S := fun h => hA (hi.mono h)
  obtain ⟨c,hc,hnotC⟩ := Set.not_subset.mp hnot
  refine ⟨c,hc,fun j n p hp => ?_⟩
  have hpS : p ∈ S := Set.mem_iUnion₂.mpr ⟨j,n,hp⟩
  have hne : a p ≠ c := by
    intro he
    exact hnotC ⟨p,hpS,he⟩
  exact (hAD (a p) (ha p) c hc hne).subset (fun _ hm => ⟨hsub p hm.1,hm.2⟩)

end

end JSP000933
