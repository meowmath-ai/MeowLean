import JSP000933CCCWitnessCapture

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def missFoot (i : OmegaTwoIndex) : Finset OmegaTwoIndex := {i}
noncomputable def edgeFoot (a : ℕ × OmegaTwoIndex × OmegaTwoIndex) : Finset OmegaTwoIndex := {a.2.1,a.2.2}

theorem map_goodCover_of_captured_r114 (F : CompleteValueMap B C) (a : OmegaTwoIndex)
    (smallX : ↥(Set.Iio a) → ℕ → B) (smallD : ↥(Set.Iio a) → B)
    (smallK : Word × Word → B) (smallC : CoverCode B)
    (bigX : OmegaTwoIndex → ℕ → C) (bigD : OmegaTwoIndex → C)
    (bigK : Word × Word → C) (bigC : CoverCode C)
    (hx : ∀ i n, F.toFun (smallX i n) = bigX i.1 n)
    (hd : ∀ i, F.toFun (smallD i) = bigD i.1)
    (hk : ∀ w, F.toFun (smallK w) = bigK w)
    (hc : ∀ n w, F.toFun (smallC n w) = bigC n w)
    (hMiss : (⨆ i : {i : OmegaTwoIndex // footprintBelow a missFoot i}, missedPoint bigX bigD bigC i.1)
      = ⨆ i, missedPoint bigX bigD bigC i)
    (hEdge : (⨆ q : {q : ℕ × OmegaTwoIndex × OmegaTwoIndex // footprintBelow a edgeFoot q},
        badEdge bigX bigD bigK bigC q.1) = ⨆ q, badEdge bigX bigD bigK bigC q) :
    F.toFun (goodCoverValue smallX smallD smallK smallC) = goodCoverValue bigX bigD bigK bigC := by
  classical
  apply compl_injective
  rw [← F.map_compl,goodCover_compl_r112,goodCover_compl_r112,F.map_sup_r93,F.map_iSup,F.map_iSup]
  have hm (i : ↥(Set.Iio a)) :
      F.toFun (missedPoint smallX smallD smallC i) = missedPoint bigX bigD bigC i.1 := by
    rw [map_missedPoint_r112]
    simp only [hx,hd,hc,missedPoint,openValue,cylinderValue]
  have he (q : ℕ × ↥(Set.Iio a) × ↥(Set.Iio a)) :
      F.toFun (badEdge smallX smallD smallK smallC q) =
        badEdge bigX bigD bigK bigC (q.1,q.2.1.1,q.2.2.1) := by
    rw [map_badEdge_r112]
    simp only [hx,hd,hk,hc,badEdge,ClosedMember,openValue,colorValue,cylinderValue]
  congr 1
  · rw [← hMiss]
    apply le_antisymm
    · apply iSup_le
      intro i
      have hi : footprintBelow a missFoot i.1 := by
        intro j hj
        exact (Finset.mem_singleton.mp hj).symm ▸ i.2
      exact le_iSup_of_le ⟨i.1,hi⟩ (hm i).le
    · apply iSup_le
      intro i
      let j : ↥(Set.Iio a) := ⟨i.1,i.2 _ (Finset.mem_singleton_self _)⟩
      exact le_iSup_of_le j (hm j).ge
  · rw [← hEdge]
    apply le_antisymm
    · apply iSup_le
      intro q
      have hq : footprintBelow a edgeFoot (q.1,q.2.1.1,q.2.2.1) := by
        intro i hi
        rcases Finset.mem_insert.mp hi with heq | hh
        · exact heq.symm ▸ q.2.1.2
        · exact (Finset.mem_singleton.mp hh).symm ▸ q.2.2.2
      exact le_iSup_of_le ⟨(q.1,q.2.1.1,q.2.2.1),hq⟩ (he q).le
    · apply iSup_le
      intro q
      have h₁ : q.1.2.1 < a := q.2 _ (Finset.mem_insert_self ..)
      have h₂ : q.1.2.2 < a := q.2 _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      let p : ℕ × ↥(Set.Iio a) × ↥(Set.Iio a) :=
        (q.1.1,⟨q.1.2.1,h₁⟩,⟨q.1.2.2,h₂⟩)
      exact le_iSup_of_le p (he p).ge

end CantorCodes
end JSP000933
