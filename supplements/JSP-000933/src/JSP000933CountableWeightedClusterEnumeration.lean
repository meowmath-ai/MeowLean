import JSP000933DensePreservesBooleanClusters

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

def zeroSample (B : Type) [CompleteBooleanAlgebra B] (n : ℕ) : BooleanSample B n :=
  ⟨fun _ _ => ⊥,fun _ => ⊥,⊥⟩

theorem exists_weightedClusterSequence_r149 (hCCC : BooleanCCC B) (K : Word × Word → B)
    {n : ℕ} (F : I → BooleanSample B n) :
    ∃ S : ℕ → BooleanSample B n,
      (∀ j, (S j).weight = ⊥ ∨ ∃ i, S j = F i) ∧
      ∀ p x, weightedCluster K F p x = weightedCluster K S p x := by
  obtain ⟨A,hA,hDense⟩ := exists_countable_weightedBoxDense_r147 hCCC F
  obtain ⟨e,he⟩ := exists_optionEnumeration_r60 A hA
  let S (j : ℕ) := match e j with
    | none => zeroSample B n
    | some i => F i
  refine ⟨S,fun j => ?_,fun p x => ?_⟩
  · cases hj : e j with
    | none => exact Or.inl (by simp only [S,hj,zeroSample])
    | some i => exact Or.inr ⟨i,by simp only [S,hj]⟩
  · rw [weightedCluster_eq_dense_r148 K F A hDense]
    have hHit (U : Fin n → Word) (V : Word) :
        weightedClusterHit K S p U V =
          weightedClusterHit K (fun i : ↥A => F i.1) p U V := by
      apply le_antisymm
      · unfold weightedClusterHit
        apply iSup_le
        intro j
        cases hj : e j with
        | none => simp [S,hj,zeroSample]
        | some i =>
          have hi : i ∈ A := (he i).mpr ⟨j,hj⟩
          exact le_iSup_of_le (⟨i,hi⟩ : ↥A) (by simp only [S,hj,le_refl])
      · unfold weightedClusterHit
        apply iSup_le
        intro i
        obtain ⟨j,hj⟩ := (he i.1).mp i.2
        exact le_iSup_of_le j (by simp only [S,hj,le_refl])
    simp only [weightedCluster,hHit]

end CantorCodes
end JSP000933
