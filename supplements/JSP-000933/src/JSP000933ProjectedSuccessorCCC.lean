import JSP000933RelativeOmegaOnePreservation
import JSP000933ProjectedLimitCCC

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B C D : Type}
  [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C] [CompleteBooleanAlgebra D]

def ProjectedAntichainCCC (π : C → B) : Prop :=
  ∀ w : OmegaOneIndex → C, (∀ i j, i<j → Disjoint (w i) (w j)) →
    unboundedValue (fun i => π (w i)) = ⊥

theorem projectedUnbounded_zero
    (π : C → B) (hMono : Monotone π) (hπ : ∀ (I : Type) (f : I → C), π (⨆ i,f i) = ⨆ i,π (f i))
    (hCCC : ProjectedAntichainCCC π) (w : OmegaOneIndex → C)
    (hw : unboundedValue w = ⊥) :
    unboundedValue (fun i => π (w i)) = ⊥ := by
  let cut (i : OmegaOneIndex) := (aboveValue w i)ᶜ
  let c := firstChoiceCell cut
  have hCover : (⨆ i,c i) = ⊤ := by
    unfold c
    rw [firstChoiceCell_join_r435]
    simpa only [unboundedValue,compl_iInf,compl_bot,cut] using congrArg (fun x : C => xᶜ) hw
  let closedTail (f : OmegaOneIndex → C) (i : OmegaOneIndex) : C :=
    ⨆ j : {j : OmegaOneIndex // i≤j},f j.val
  have hBound (i : OmegaOneIndex) : w i ≤ closedTail c i := by
    calc
      w i = w i ⊓ (⨆ j,c j) := by rw [hCover,inf_top_eq]
      _ = ⨆ j,w i ⊓ c j := inf_iSup_eq _ _
      _ ≤ _ := by
        apply iSup_le
        intro j
        by_cases hj : i≤j
        · exact inf_le_right.trans (le_iSup (fun k : {k : OmegaOneIndex // i ≤ k} => c k.val) ⟨j,hj⟩)
        · have hji : j< i := lt_of_not_ge hj
          have hw' : w i ≤ aboveValue w j :=
            le_iSup (fun k : {k : OmegaOneIndex // j < k} => w k.val) ⟨i,hji⟩
          have hc' : c j ≤ (aboveValue w j)ᶜ := firstChoiceCell_le_r435 cut j
          exact (inf_le_inf hw' hc').trans
            ((disjoint_iff_inf_le.mp disjoint_compl_right).trans bot_le)
  have hPi (i : OmegaOneIndex) :
      π (w i) ≤ ⨆ j : {j : OmegaOneIndex // i≤j}, π (c j.val) := by
    apply (hMono (hBound i)).trans
    unfold closedTail
    rw [hπ]
  have hU : unboundedValue (fun i => π (w i)) ≤ unboundedValue (fun i => π (c i)) := by
    apply le_iInf
    intro i
    apply (iInf_le _ i).trans
    apply iSup_le
    intro j
    apply (hPi j.val).trans
    exact iSup_le (fun k => le_iSup (fun l : {l : OmegaOneIndex // i < l} => π (c l.val))
      ⟨k.val,j.property.trans_le k.property⟩)
  exact le_bot_iff.mp (hU.trans_eq (hCCC c (firstChoiceCell_disjoint_r435 cut)))

theorem projectedAntichainCCC_comp
    (π : C → B) (σ : D → C) (hMono : Monotone π)
    (hπ : ∀ (I : Type) (f : I → C), π (⨆ i,f i) = ⨆ i,π (f i))
    (hP : ProjectedAntichainCCC π) (hQ : ProjectedAntichainCCC σ) :
    ProjectedAntichainCCC (π ∘ σ) :=
  fun w hw => projectedUnbounded_zero π hMono hπ hP _ (hQ w hw)

end RelativeOCA
end JSP000933
