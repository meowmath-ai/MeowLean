import JSP000933RelativeChoiceNormalization
import JSP000933RelativeUniformCutoffs

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

structure DiscreteChoiceOn (I : Type) (m : B) where
  value : I→B
  disjoint : Pairwise (fun i j => Disjoint (value i) (value j))
  each_le : ∀ i,value i≤ m
  covers : (⨆ i,value i)=m

theorem exists_discreteChoiceOn_r445 {I : Type} (m : B) (U : I→B)
    (h : m≤⨆ i,U i) :
    ∃ C : DiscreteChoiceOn I m,∀ i,C.value i≤U i := by
  obtain ⟨L,hL⟩ := exists_wellFoundedLT I
  letI : LinearOrder I := L
  letI : WellFoundedLT I := hL
  let W (i : I) := m⊓U i
  let v := firstChoiceCell W
  have hV (i : I) : v i≤W i := firstChoiceCell_le_r435 W i
  have hPair : Pairwise (fun i j => Disjoint (v i) (v j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hl | hr
    · exact firstChoiceCell_disjoint_r435 W i j hl
    · exact (firstChoiceCell_disjoint_r435 W j i hr).symm
  have hCover : (⨆ i,v i)=m := by
    rw [firstChoiceCell_join_r435]
    exact (inf_iSup_eq _ _).symm.trans (inf_eq_left.mpr h)
  exact ⟨⟨v,hPair,fun i => (hV i).trans inf_le_left,hCover⟩,
    fun i => (hV i).trans inf_le_right⟩

noncomputable def guardByChoice {I : Type} {m : B} (C : DiscreteChoiceOn I m)
    (v : I→B) : B :=
  ⨅ i,(C.value i)ᶜ⊔v i

theorem guardByChoice_onCell_r445 {I : Type} {m : B} (C : DiscreteChoiceOn I m)
    (v : I→B) (i : I) :
    C.value i⊓v i≤guardByChoice C v := by
  apply le_iInf
  intro j
  by_cases hij : i=j
  · subst j
    exact inf_le_right.trans le_sup_right
  · exact inf_le_left.trans ((le_compl_iff_disjoint_right.mpr (C.disjoint hij)).trans le_sup_left)

theorem guardByChoice_elim_r445 {I : Type} {m : B} (C : DiscreteChoiceOn I m)
    (v : I→B) (i : I) :
    guardByChoice C v⊓C.value i≤v i :=
  (le_materialImp_iff_r126 _ _ _).mp (iInf_le _ i)

theorem guardByChoice_mono_r445 {I : Type} {m : B} (C : DiscreteChoiceOn I m)
    {v w : I→B} (h : ∀ i,v i≤w i) : guardByChoice C v≤guardByChoice C w := by
  apply le_iInf
  intro i
  exact (iInf_le _ i).trans (sup_le_sup le_rfl (h i))

theorem guardByChoice_coversCutoffs_r445 {I : Type} {m : B} (C : DiscreteChoiceOn I m)
    (V : I→OmegaOneIndex→B) (hV : ∀ i,C.value i≤⨆ b,V i b) :
    m≤⨆ b,guardByChoice C (fun i => V i b) := by
  apply C.covers.ge.trans
  apply iSup_le
  intro i
  apply (le_inf le_rfl (hV i)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro b
  exact le_iSup_of_le b (guardByChoice_onCell_r445 C (fun i => V i b) i)

end RelativeOCA
end JSP000933
