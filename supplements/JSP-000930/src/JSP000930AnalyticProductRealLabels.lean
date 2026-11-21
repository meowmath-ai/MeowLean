import JSP000930EarlierCenterBudget

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B]

def blankSymbolicTrace (J : Type) : SymbolicTrace J :=
  ⟨[],[],0,1,by norm_num,List.nodup_nil⟩

theorem blankSymbolicTrace_support (A : J → Prop) : SymbolicAt A (blankSymbolicTrace J) := by
  intro i hi
  simp [blankSymbolicTrace] at hi

theorem blankSymbolicTrace_valid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) :
    polyValid site H (decodeSymbolicTrace site H (blankSymbolicTrace J)) = ⊤ := by
  apply top_unique
  apply symbolicTrace_valid_from_environment _ _ _ _
  · intro j
    rcases j with j|j <;> exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j

set_option maxHeartbeats 350000 in
theorem analyticProduct_refine_to_real_labels {A : J → Prop}
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (p : AnalyticRowTotal site H A) :
    ∃ q : AnalyticRowTotal site H A, q ≤ p ∧ q.mask = p.mask ∧
      ∀ i,∃ t : SymbolicTrace J,(q.trace i).val = some t := by
  let Q (i : I) := supportedSymbolicQ site (H i) A
  let r (i : I) : SupportedSymbolic J A :=
    match (p.trace i).val with
    | some t => p.trace i
    | none => ⟨some (blankSymbolicTrace J),blankSymbolicTrace_support A⟩
  have hR (i : I) : p.mask ≤ (Q i).refines (r i) (p.trace i) := by
    have h := p.valid.trans (iInf_le _ i)
    have hn : p.mask ≤ (symbolicPolynomialQ site (H i)).valid (p.trace i).val := h
    cases he : (p.trace i).val with
    | none =>
      change p.mask ≤ (symbolicPolynomialQ site (H i)).refines (r i).val (p.trace i).val
      have hrv : (r i).val = some (blankSymbolicTrace J) := by simp only [r,he]
      rw [hrv,he]
      change p.mask ≤ polyValid site (H i) (decodeSymbolicTrace site (H i) (blankSymbolicTrace J))
      rw [blankSymbolicTrace_valid]
      exact le_top
    | some t =>
      have heq : r i = p.trace i := by simp only [r,he]
      rw [heq]
      exact h.trans ((Q i).refl _)
  let v : AnalyticRowTotal site H A :=
    ⟨p.mask,r,p.nonzero,le_iInf (fun i =>
      ((hR i).trans ((Q i).refine_valid _ _)).trans inf_le_left)⟩
  refine ⟨v,⟨le_rfl,le_iInf hR⟩,rfl,?_⟩
  intro i
  cases h : (p.trace i).val with
  | none => exact ⟨blankSymbolicTrace J,by simp only [v,r,h]⟩
  | some t => exact ⟨t,by simp only [v,r,h]⟩

end JSP000930.Negative
