import JSP000933StrongCorrectDiamondGuess

namespace JSP000933
namespace CantorCodes

open BooleanCompletion

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem map_goodCoverValue_r166 (F : CompleteValueMap B C)
    (x : I → ℕ → B) (D : I → B) (K : Word × Word → B) (q : CoverCode B) :
    F.toFun (goodCoverValue x D K q) =
      goodCoverValue (fun i n => F.toFun (x i n)) (fun i => F.toFun (D i))
        (fun w => F.toFun (K w)) (fun n w => F.toFun (q n w)) := by
  simp only [goodCoverValue,coverValue,independentValue,ClosedMember,F.map_inf,
    F.map_iInf,F.map_iSup,F.map_sup_r93,F.map_compl,map_colorValue_r105,map_openValue_r105]

theorem indexed_goodCoverValue_eq_of_surj_r166 (x : I → ℕ → B) (hX : Function.Surjective x)
    (D : (ℕ → B) → B) (K : Word × Word → B) (q : CoverCode B) :
    goodCoverValue x (fun i => D (x i)) K q = goodCoverValue id D K q := by
  have hCover : coverValue x (fun i => D (x i)) q = coverValue id D q := by
    apply le_antisymm
    · apply le_iInf
      intro z
      obtain ⟨i,rfl⟩ := hX z
      exact iInf_le _ i
    · apply le_iInf
      intro i
      exact iInf_le _ (x i)
  have hInd : independentValue x (fun i => D (x i)) K q = independentValue id D K q := by
    apply le_antisymm
    · apply le_iInf
      rintro ⟨n,u,v⟩
      obtain ⟨i,rfl⟩ := hX u
      obtain ⟨j,rfl⟩ := hX v
      exact iInf_le _ (n,i,j)
    · apply le_iInf
      rintro ⟨n,i,j⟩
      exact iInf_le _ (n,x i,x j)
  exact congrArg₂ (· ⊓ ·) hCover hInd

theorem saturatedDomain_le_extensional_r166 (x : I → ℕ → B)
    (d : I → B) (D : (ℕ → B) → B) (hD : RealTestExt D)
    (hMem : ∀ i, d i ≤ D (x i)) (z : ℕ → B) :
    saturatedDomain x d z ≤ D z := by
  apply iSup_le
  intro i
  let p := d i ⊓ realEqValue z (x i)
  have hEq : p ⊓ D z = p ⊓ D (x i) := hD p z (x i) inf_le_right
  exact (le_inf le_rfl (inf_le_left.trans (hMem i))).trans (hEq.ge.trans inf_le_right)

end CantorCodes
end JSP000933
