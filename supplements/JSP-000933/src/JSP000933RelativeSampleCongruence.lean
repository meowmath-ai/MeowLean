import JSP000933RelativeCodeSchedules
import JSP000933WeightedTupleDenseTests

namespace JSP000933
namespace RelativeOCA

open CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

structure SampleAgreesOn {n : ℕ} (m : B) (s t : BooleanSample B n) : Prop where
  stems : ∀ i,m≤realEqValue (s.stem i) (t.stem i)
  tip : m≤realEqValue s.tip t.tip
  weight : m⊓s.weight=m⊓t.weight

theorem tableAgreement_samples_r450 {n : ℕ} (F G : ℕ→BooleanSample B n) (m : B)
    (h : m≤tableAgreement (sampleTable F) (sampleTable G)) (j : ℕ) :
    SampleAgreesOn m (F j) (G j) := by
  have hA := (tableAgreement_spec_r441 _ _ _).mp h
  refine ⟨fun i => (le_realEqValue_iff_r126 _ _ _).mpr (fun k => ?_),
    (le_realEqValue_iff_r126 _ _ _).mpr (fun k => ?_),?_⟩
  · exact hA (j,.inl (i,k))
  · exact hA (j,.inr (.inl k))
  · exact hA (j,.inr (.inr ()))

theorem listCylinder_mask_r450 {m : B} {x y : ℕ→B}
    (h : m≤realEqValue x y) (l : List Word) :
    m⊓listCylinder x l=m⊓listCylinder y l := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change m⊓(cylinderValue x w⊓listCylinder x l)=
      m⊓(cylinderValue y w⊓listCylinder y l)
    exact mask_inf_congr_r126 (mask_cylinder_congr_r127 h w) ih

theorem sampleBox_mask_r450 {n : ℕ} {m : B} {s t : BooleanSample B n}
    (h : SampleAgreesOn m s t) (U : Fin n→List Word) (V : List Word) :
    m⊓sampleBox s U V=m⊓sampleBox t U V := by
  unfold sampleBox multiStemCylinder
  exact mask_inf_congr_r126 h.weight (mask_inf_congr_r126
    (mask_iInf_congr_r126 (fun i => listCylinder_mask_r450 (h.stems i) (U i)))
    (listCylinder_mask_r450 h.tip V))

theorem mask_sup_congr_r450 {m x y u v : B} (h₁ : m⊓x=m⊓u) (h₂ : m⊓y=m⊓v) :
    m⊓(x⊔y)=m⊓(u⊔v) := by
  rw [inf_sup_left,inf_sup_left,h₁,h₂]

theorem weightedClusterHit_mask_r450 {I : Type} {n : ℕ} (m : B)
    (F G : I→BooleanSample B n) (h : ∀ i,SampleAgreesOn m (F i) (G i))
    (K : Word×Word→B) (p : Fin n→ℕ→B) (U : Fin n→Word) (V : Word) :
    m⊓weightedClusterHit K F p U V=m⊓weightedClusterHit K G p U V := by
  unfold weightedClusterHit
  apply mask_iSup_congr_r126
  intro i
  apply mask_inf_congr_r126
  · apply mask_inf_congr_r126 (h i).weight
    unfold matchedValue
    apply mask_iInf_congr_r126
    intro j
    exact mask_colorValue_congr_r127 K (by rw [realEqValue_refl_r127]; exact le_top) ((h i).stems j)
  · apply mask_inf_congr_r126
    · unfold stemCylinder
      exact mask_iInf_congr_r126 (fun j => mask_cylinder_congr_r127 ((h i).stems j) (U j))
    · exact mask_cylinder_congr_r127 (h i).tip V

theorem weightedCluster_mask_r450 {I : Type} {n : ℕ} (m : B)
    (F G : I→BooleanSample B n) (h : ∀ i,SampleAgreesOn m (F i) (G i))
    (K : Word×Word→B) (p : Fin n→ℕ→B) (x : ℕ→B) :
    m⊓weightedCluster K F p x=m⊓weightedCluster K G p x := by
  unfold weightedCluster
  apply mask_iInf_congr_r126
  intro U
  apply mask_iInf_congr_r126
  intro V
  exact mask_sup_congr_r450 rfl (weightedClusterHit_mask_r450 m F G h K p U V)

end RelativeOCA
end JSP000933
