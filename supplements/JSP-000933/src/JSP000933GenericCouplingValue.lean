import JSP000933CouplingForcing

namespace JSP000933
namespace PositiveForcing

open Erdos1123 BooleanCompletion

theorem top_of_dense_images_r184 {P : Type*} [Preorder P] (a : RO P)
    (h : ∀ p : P, ∃ q : P, q ≤ p ∧ imageCondition q ≤ a) : a = ⊤ := by
  classical
  apply top_unique
  by_contra hn
  have hc : aᶜ ≠ ⊥ := by
    intro he
    exact hn (by rw [← compl_compl a,he,compl_bot])
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 aᶜ hc
  obtain ⟨q,hqp,hqa⟩ := h p
  have hq := (imageCondition_mono_r50 hqp).trans hp
  exact imageCondition_ne_bot_r50 q
    (le_bot_iff.mp ((le_inf hqa hq).trans_eq (inf_compl_eq_bot' (x := a))))

variable {W V : WeightSequence ℕ}

noncomputable def pairValue (a : Set ℕ × Set ℕ) : RO (CouplingCondition W V) :=
  ⨆ p : {p : CouplingCondition W V // a ∈ p.pairs}, imageCondition p.1

theorem image_le_pairValue_r184 (p : CouplingCondition W V) {a : Set ℕ × Set ℕ}
    (ha : a ∈ p.pairs) : imageCondition p ≤ pairValue a :=
  le_iSup (fun q : {q : CouplingCondition W V // a ∈ q.pairs} => imageCondition q.val) ⟨p,ha⟩

theorem pairValue_left_total_r184 (hW : BlockStructure W) (hV : BlockStructure V) (A : Set ℕ) :
    (⨆ B : Set ℕ, pairValue (W := W) (V := V) (A,B)) = ⊤ := by
  apply top_of_dense_images_r184
  intro p
  obtain ⟨q,hqp,⟨B,hB⟩,_⟩ := extend_both_r183 hW hV p A
  exact ⟨q,hqp,le_iSup_of_le B (image_le_pairValue_r184 q hB)⟩

theorem pairValue_right_total_r184 (hW : BlockStructure W) (hV : BlockStructure V) (B : Set ℕ) :
    (⨆ A : Set ℕ, pairValue (W := W) (V := V) (A,B)) = ⊤ := by
  apply top_of_dense_images_r184
  intro p
  obtain ⟨q,hqp,_,⟨A,hA⟩⟩ := extend_both_r183 hW hV p B
  exact ⟨q,hqp,le_iSup_of_le A (image_le_pairValue_r184 q hA)⟩

theorem pairValue_disagree_inf_bot_r184 (a b : Set ℕ × Set ℕ)
    (hBad : ¬ (W.IsNull (a.1 \ b.1) ↔ V.IsNull (a.2 \ b.2))) :
    pairValue (W := W) (V := V) a ⊓ pairValue (W := W) (V := V) b = ⊥ := by
  apply le_bot_iff.mp
  simp only [pairValue,iSup_inf_iSup]
  apply iSup_le
  intro ij
  apply disjoint_iff_inf_le.mp
  by_contra hN
  obtain ⟨q,hqi,hqj⟩ := (compatible_iff_not_disjoint_r50 _ _).mpr hN
  exact hBad (difference_null_iff_r183 q (hqi ij.1.2) (hqj ij.2.2))

end PositiveForcing
end JSP000933
