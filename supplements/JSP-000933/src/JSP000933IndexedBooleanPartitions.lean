import JSP000933MixingDisjointRefinement

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

structure IndexedPartition (B I : Type) [CompleteBooleanAlgebra B] (p : B) where
  weight : I → B
  covers : (⨆ i, weight i) = p
  separate : ∀ i j, i ≠ j → Disjoint (weight i) (weight j)

theorem IndexedPartition.weight_le_r215 {p : B} (P : IndexedPartition B I p) (i : I) :
    P.weight i ≤ p :=
  (le_iSup P.weight i).trans_eq P.covers

theorem exists_indexedPartition_of_join_r215 (p : B) (T : I → B) (h : p ≤ ⨆ i, T i) :
    ∃ P : IndexedPartition B I p, ∀ i, P.weight i ≤ T i := by
  classical
  obtain ⟨M,hM,hDis,hSum⟩ := exists_disjoint_witnessRefinement_r137 p T h
  have hW (a : ↥M) : ∃ i, a.val ≤ T i := (hM a.val a.property).2.2
  choose f hf using hW
  let cell (i : I) (a : ↥M) : B := if f a = i then a.val else ⊥
  let w (i : I) : B := ⨆ a : ↥M, cell i a
  have hBound (i : I) : w i ≤ p := by
    apply iSup_le
    intro a
    by_cases he : f a = i
    · simpa [cell,he] using (hM a.val a.property).2.1
    · simp [cell,he]
  have hCover : (⨆ i, w i) = p := by
    apply le_antisymm (iSup_le hBound)
    rw [← hSum]
    apply sSup_le
    intro a ha
    let t : ↥M := ⟨a,ha⟩
    apply le_iSup_of_le (f t)
    apply le_iSup_of_le t
    simp [cell,t]
  have hSeparate (i j : I) (hne : i ≠ j) : Disjoint (w i) (w j) := by
    apply disjoint_iff_inf_le.mpr
    change (⨆ a : ↥M, cell i a) ⊓ (⨆ a : ↥M, cell j a) ≤ ⊥
    rw [iSup_inf_iSup]
    apply iSup_le
    intro ab
    by_cases h₁ : f ab.1 = i
    · by_cases h₂ : f ab.2 = j
      · have hv : ab.1.val ≠ ab.2.val := by
          intro he
          exact hne (h₁.symm.trans ((congrArg f (Subtype.ext he)).trans h₂))
        simpa [cell,h₁,h₂] using
          disjoint_iff_inf_le.mp (hDis _ ab.1.2 _ ab.2.2 hv)
      · simp [cell,h₂]
    · simp [cell,h₁]
  refine ⟨⟨w,hCover,hSeparate⟩,?_⟩
  intro i
  apply iSup_le
  intro a
  by_cases he : f a = i
  · simpa [cell,he] using hf a
  · simp [cell,he]

end CantorCodes
end JSP000933
