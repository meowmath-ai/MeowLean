import JSP000933RelativeSampleCongruence
import JSP000933RelativeDiscreteChoices

namespace JSP000933
namespace RelativeOCA

open CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def mixedSample {I : Type} {n : ℕ} {m : B} (C : DiscreteChoiceOn I m)
    (F : I→BooleanSample B n) : BooleanSample B n :=
  ⟨fun j => mixIndexedReal C.value (fun i => (F i).stem j),
    mixIndexedReal C.value (fun i => (F i).tip),m⟩

theorem mixedSample_onCell_r451 {I : Type} {n : ℕ} {m : B} (C : DiscreteChoiceOn I m)
    (F : I→BooleanSample B n) (i : I) (h : C.value i≤(F i).weight) :
    SampleAgreesOn (C.value i) (mixedSample C F) (F i) := by
  refine ⟨fun j => mixIndexedReal_on_weight_r439 C.value C.disjoint _ i,
    mixIndexedReal_on_weight_r439 C.value C.disjoint _ i,?_⟩
  change C.value i⊓m=C.value i⊓(F i).weight
  rw [inf_eq_left.mpr (C.each_le i),inf_eq_left.mpr h]

theorem mixedSample_box_le_r451 {I : Type} {n : ℕ} {m : B} (C : DiscreteChoiceOn I m)
    (F : I→BooleanSample B n) (h : ∀ i,C.value i≤(F i).weight)
    (U : Fin n→List Word) (V : List Word) :
    sampleBox (mixedSample C F) U V≤⨆ i,sampleBox (F i) U V := by
  let a := sampleBox (mixedSample C F) U V
  have hm : a≤ m := inf_le_left
  have ha : a≤(⨆ i,C.value i)⊓a := le_inf (hm.trans_eq C.covers.symm) le_rfl
  apply ha.trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro i
  change C.value i⊓sampleBox (mixedSample C F) U V≤_
  rw [sampleBox_mask_r450 (mixedSample_onCell_r451 C F i (h i))]
  exact inf_le_right.trans (le_iSup (fun j => sampleBox (F j) U V) i)

theorem mixedSample_coversChosenBox_r451 {I : Type} {n : ℕ} {m : B} (C : DiscreteChoiceOn I m)
    (F : I→BooleanSample B n) (U : Fin n→List Word) (V : List Word)
    (h : ∀ i,C.value i ≤ sampleBox (F i) U V) :
    m ≤ sampleBox (mixedSample C F) U V := by
  apply C.covers.ge.trans
  apply iSup_le
  intro i
  have hE := sampleBox_mask_r450
    (mixedSample_onCell_r451 C F i ((h i).trans inf_le_left)) U V
  exact ((le_inf le_rfl (h i)).trans_eq hE.symm).trans inf_le_right

theorem exists_countable_mixedWeightedBoxDense_r451 {I : Type} {n : ℕ}
    (F : I→BooleanSample B n) :
    ∃ G : ℕ→BooleanSample B n,∀ (U : Fin n→List Word) (V : List Word),
      (⨆ j,sampleBox (G j) U V)=⨆ i,sampleBox (F i) U V := by
  classical
  let Box := (Fin n→List Word)×List Word
  let val (b : Box) := ⨆ i,sampleBox (F i) b.1 b.2
  have hPick (b : Box) : ∃ C : DiscreteChoiceOn I (val b),
      ∀ i,C.value i ≤ sampleBox (F i) b.1 b.2 :=
    exists_discreteChoiceOn_r445 _ _ le_rfl
  choose C hC using hPick
  let G (j : ℕ) : BooleanSample B n :=
    match (Encodable.decode j : Option Box) with
    | none => ⟨fun _ _ => ⊥,fun _ => ⊥,⊥⟩
    | some b => mixedSample (C b) F
  refine ⟨G,fun U V => ?_⟩
  apply le_antisymm
  · apply iSup_le
    intro j
    cases h : (Encodable.decode j : Option Box) with
    | none => simp only [G,h,sampleBox,bot_inf_eq,bot_le]
    | some b =>
      simpa only [G,h] using mixedSample_box_le_r451 (C b) F
        (fun i => (hC b i).trans inf_le_left) U V
  · let b : Box := (U,V)
    apply le_iSup_of_le (Encodable.encode b)
    simpa only [G,Encodable.encodek] using mixedSample_coversChosenBox_r451 (C b) F U V (hC b)

end RelativeOCA
end JSP000933
