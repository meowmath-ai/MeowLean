import JSP000933FiniteOpenRectangleWitnesses
import Mathlib.Order.Zorn

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem exists_disjoint_witnessRefinement_r137 (p : B) (term : I → B) (h : p ≤ ⨆ i, term i) :
    ∃ M : Set B, (∀ a ∈ M, a ≠ ⊥ ∧ a ≤ p ∧ ∃ i, a ≤ term i) ∧
      (∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b) ∧ sSup M = p := by
  classical
  let Good : Set B := {a | a ≠ ⊥ ∧ a ≤ p ∧ ∃ i, a ≤ term i}
  let Families : Set (Set B) := {M | M ⊆ Good ∧ ∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b}
  have hChain : ∀ C ⊆ Families, IsChain (· ⊆ ·) C → ∃ U ∈ Families, ∀ S ∈ C, S ⊆ U := by
    intro C hc hch
    refine ⟨⋃₀ C,⟨?_,?_⟩,fun _ hS => Set.subset_sUnion_of_mem hS⟩
    · rintro x ⟨S,hS,hx⟩
      exact (hc hS).1 hx
    · rintro a ⟨S,hS,ha⟩ b ⟨T,hT,hb⟩ hne
      by_cases he : S = T
      · subst T
        exact (hc hS).2 a ha b hb hne
      · rcases hch hS hT he with hST | hTS
        · exact (hc hT).2 a (hST ha) b hb hne
        · exact (hc hS).2 a ha b (hTS hb) hne
  obtain ⟨M,hM⟩ := zorn_subset Families hChain
  refine ⟨M,hM.prop.1,hM.prop.2,le_antisymm ?_ ?_⟩
  · exact sSup_le (fun b hb => (hM.prop.1 hb).2.1)
  · by_contra hN
    let r := p ⊓ (sSup M)ᶜ
    have hr : r ≠ ⊥ := by
      intro he
      apply hN
      have hd : Disjoint p (sSup M)ᶜ := disjoint_iff_inf_le.mpr he.le
      exact (le_compl_iff_disjoint_right.mpr hd).trans_eq (compl_compl _)
    obtain ⟨i,b,hb,hbr,hi⟩ :=
      exists_nonzero_below_choice_r135 r hr term (inf_le_left.trans h)
    have hDis (a : B) (ha : a ∈ M) : Disjoint b a :=
      le_compl_iff_disjoint_right.mp
        (hbr.trans (inf_le_right.trans (compl_le_compl (le_sSup ha))))
    have hNot : b ∉ M := fun hbM => hb (disjoint_self.mp (hDis b hbM))
    have hInsert : insert b M ∈ Families := by
      refine ⟨?_,?_⟩
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hb,hbr.trans inf_le_left,i,hi⟩
        · exact hM.prop.1 ha
      · intro a ha c hc hne
        rcases Set.mem_insert_iff.mp ha with hEq | haM
        · subst a
          rcases Set.mem_insert_iff.mp hc with hEq | hcM
          · exact False.elim (hne hEq.symm)
          · exact hDis c hcM
        · rcases Set.mem_insert_iff.mp hc with hEq | hcM
          · subst c
            exact (hDis a haM).symm
          · exact hM.prop.2 a haM c hcM hne
    have he : M = insert b M := hM.eq_of_subset hInsert (Set.subset_insert _ _)
    exact hNot (he.symm ▸ Set.mem_insert b M)

end CantorCodes
end JSP000933
