import JSP000933RelativeCCCProjection

namespace JSP000933
namespace RelativeOCA

variable {A B : Type} [Preorder A] [CompleteBooleanAlgebra B]

noncomputable def priorChoiceJoin (v : A→B) (i : A) : B :=
  ⨆ j : ↥(Set.Iio i),v j.val

noncomputable def firstChoiceCell (v : A→B) (i : A) : B :=
  v i⊓(priorChoiceJoin v i)ᶜ

theorem firstChoiceCell_le_r435 (v : A→B) (i : A) : firstChoiceCell v i≤v i := inf_le_left

theorem firstChoiceCell_disjoint_r435 (v : A→B) (i j : A) (hij : i<j) :
    Disjoint (firstChoiceCell v i) (firstChoiceCell v j) := by
  have h1 : firstChoiceCell v i≤priorChoiceJoin v j :=
    (firstChoiceCell_le_r435 v i).trans (le_iSup (fun k : ↥(Set.Iio j) => v k.val) ⟨i,hij⟩)
  have h2 : firstChoiceCell v j≤(priorChoiceJoin v j)ᶜ := inf_le_right
  exact disjoint_iff_inf_le.mpr ((inf_le_inf h1 h2).trans
    (disjoint_iff_inf_le.mp (disjoint_compl_right :
      Disjoint (priorChoiceJoin v j) (priorChoiceJoin v j)ᶜ)))

theorem firstChoiceCell_join_r435 [WellFoundedLT A] (v : A→B) :
    (⨆ i,firstChoiceCell v i)=⨆ i,v i := by
  apply le_antisymm (iSup_le (fun i => (firstChoiceCell_le_r435 v i).trans (le_iSup v i)))
  apply iSup_le
  intro i
  refine wellFounded_lt.induction (C := fun j => v j ≤ ⨆ k, firstChoiceCell v k) i ?_
  intro j ih
  have hP : priorChoiceJoin v j≤⨆ i,firstChoiceCell v i :=
    iSup_le (fun a => ih a.val a.property)
  calc
    v j = (v j⊓priorChoiceJoin v j)⊔firstChoiceCell v j :=
      Eq.symm sup_inf_inf_compl
    _ ≤ _ := sup_le (inf_le_right.trans hP) (le_iSup (firstChoiceCell v) j)

end RelativeOCA
end JSP000933
