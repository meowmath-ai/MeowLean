import JSP000930IncomingSymbolicGeometry

namespace JSP000930.Negative

open JSP000933.MarkedForcing

variable {B I : Type} [CompleteBooleanAlgebra B] {N : I → Type}

noncomputable def rowProductQ (Q : ∀ i,ValuedPoset B (N i)) : ValuedPoset B (∀ i,N i) where
  valid p := ⨅ i,(Q i).valid (p i)
  refines p q := ⨅ i,(Q i).refines (p i) (q i)
  refine_valid := by
    intro p q
    apply le_inf
    · exact le_iInf (fun i => (iInf_le _ i).trans (((Q i).refine_valid _ _).trans inf_le_left))
    · exact le_iInf (fun i => (iInf_le _ i).trans (((Q i).refine_valid _ _).trans inf_le_right))
  refl := by
    intro p
    exact le_iInf (fun i => (iInf_le _ i).trans ((Q i).refl _))
  trans := by
    intro p q r
    apply le_iInf
    intro i
    exact (le_inf (inf_le_left.trans (iInf_le _ i)) (inf_le_right.trans (iInf_le _ i))).trans
      ((Q i).trans _ _ _)
  weakest i := (Q i).weakest
  weakest_valid := by
    apply top_unique
    exact le_iInf (fun i => (Q i).weakest_valid.ge)
  weaker := by
    intro p
    exact le_iInf (fun i => (iInf_le _ i).trans ((Q i).weaker _))

theorem le_product_valid_iff (Q : ∀ i,ValuedPoset B (N i)) (m : B) (p : ∀ i,N i) :
    m ≤ (rowProductQ Q).valid p ↔ ∀ i,m ≤ (Q i).valid (p i) :=
  ⟨fun h i => h.trans (iInf_le _ i),le_iInf⟩

theorem le_product_refines_iff (Q : ∀ i,ValuedPoset B (N i))
    (m : B) (p q : ∀ i,N i) :
    m ≤ (rowProductQ Q).refines p q ↔ ∀ i,m ≤ (Q i).refines (p i) (q i) :=
  ⟨fun h i => h.trans (iInf_le _ i),le_iInf⟩

end JSP000930.Negative
