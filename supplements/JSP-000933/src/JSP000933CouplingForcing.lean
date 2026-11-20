import JSP000933BooleanCompletion
import ErdosProblems.Erdos1123.LogarithmicBlocks

namespace JSP000933
namespace PositiveForcing

open Erdos1123 BooleanCompletion

structure CouplingCondition (W V : WeightSequence ℕ) where
  pairs : Set (Set ℕ × Set ℕ)
  countable_pairs : pairs.Countable
  good : Coupling.GoodRelation (W := W) (V := V) pairs

variable {W V : WeightSequence ℕ}

instance : Preorder (CouplingCondition W V) where
  le p q := q.pairs ⊆ p.pairs
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

instance : Nonempty (CouplingCondition W V) :=
  ⟨⟨∅,Set.countable_empty,Or.inl rfl⟩⟩

def initialCondition (hW : BlockStructure W) (hV : BlockStructure V) : CouplingCondition W V where
  pairs := (Coupling.initial hW hV).algebra
  countable_pairs := (Coupling.initial_countable hW hV).to_set
  good := Or.inr ⟨Coupling.initial hW hV,rfl⟩

theorem countableDirected_lower_r183 {I : Type} [Countable I]
    (p : I → CouplingCondition W V) (h : Directed (· ≥ ·) p) :
    ∃ q : CouplingCondition W V, ∀ i, q ≤ p i := by
  let r (i : I) := (p i).pairs
  have hd : Directed (· ⊆ ·) r := by
    intro i j
    obtain ⟨k,hi,hj⟩ := h i j
    exact ⟨k,hi,hj⟩
  let q : CouplingCondition W V :=
    ⟨⋃ i, r i, Set.countable_iUnion (fun i => (p i).countable_pairs),
      Coupling.goodRelation_iUnion r hd (fun i => (p i).good)⟩
  exact ⟨q,fun i _ hz => Set.mem_iUnion.mpr ⟨i,hz⟩⟩

theorem descending_lower_r183 (p : ℕ → CouplingCondition W V) (h : Antitone p) :
    ∃ q : CouplingCondition W V, ∀ i, q ≤ p i :=
  countableDirected_lower_r183 p (fun i j => ⟨max i j,h (le_max_left _ _),h (le_max_right _ _)⟩)

theorem extend_both_r183 (hW : BlockStructure W) (hV : BlockStructure V)
    (p : CouplingCondition W V) (A : Set ℕ) :
    ∃ q : CouplingCondition W V, q ≤ p ∧
      (∃ B, (A,B) ∈ q.pairs) ∧ (∃ B, (B,A) ∈ q.pairs) := by
  classical
  rcases p.good with h | ⟨C,hC⟩
  · obtain ⟨D,hDc,_,hLeft,hRight⟩ :=
      Coupling.countable_forth_and_back (Coupling.initial hW hV) hW hV A
    let q : CouplingCondition W V := ⟨D.algebra,hDc.to_set,Or.inr ⟨D,rfl⟩⟩
    have hQ : q ≤ p := by
      change p.pairs ⊆ q.pairs
      simp only [h,Set.empty_subset]
    exact ⟨q,hQ,hLeft,hRight⟩
  · letI : Countable C.algebra := by
      have hcount : (C.algebra : Set (Set ℕ × Set ℕ)).Countable := by
        rw [hC]
        exact p.countable_pairs
      exact hcount.to_subtype
    obtain ⟨D,hDc,hCD,hLeft,hRight⟩ := Coupling.countable_forth_and_back C hW hV A
    let q : CouplingCondition W V := ⟨D.algebra,hDc.to_set,Or.inr ⟨D,rfl⟩⟩
    refine ⟨q,?_,hLeft,hRight⟩
    intro x hx
    exact hCD ((C.mem_iff_carrier_eq hC x).mpr hx)

theorem difference_null_iff_r183 (p : CouplingCondition W V)
    {a b : Set ℕ × Set ℕ} (ha : a ∈ p.pairs) (hb : b ∈ p.pairs) :
    W.IsNull (a.1 \ b.1) ↔ V.IsNull (a.2 \ b.2) := by
  obtain ⟨C,hC⟩ := Coupling.goodRelation_of_mem p.good ha
  have haa := (C.mem_iff_carrier_eq hC a).mpr ha
  have hbb := (C.mem_iff_carrier_eq hC b).mpr hb
  have hc : a ⊓ bᶜ ∈ C.algebra := C.algebra.inf_mem haa (C.algebra.compl_mem hbb)
  exact C.null_iff hc

end PositiveForcing
end JSP000933
