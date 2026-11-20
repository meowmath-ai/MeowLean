import JSP000933CountableWeightedClusterEnumeration

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem samples_of_clusterEdge_r150 (K : Word × Word → B) {n : ℕ}
    (S : I → BooleanSample B n) (stem : Fin n → ℕ → B) (x y : ℕ → B)
    (p : B) (hp : p ≠ ⊥)
    (hx : p ≤ weightedCluster K S stem x) (hy : p ≤ weightedCluster K S stem y)
    (hxy : p ≤ colorValue K x y)
    (reverse : ∀ j : I, ∀ i : Fin n, (S j).weight ⊓ colorValue K (stem i) ((S j).stem i) ≤
      colorValue K ((S j).stem i) (stem i)) :
    ∃ j k : I, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ (S j).weight ∧ q ≤ (S k).weight ∧
      q ≤ matchedValue K (S j).stem (S k).stem ∧ q ≤ colorValue K (S j).tip (S k).tip := by
  obtain ⟨uv,a,ha,hap,haBoxes⟩ := exists_nonzero_below_choice_r135 p hp
    (fun w => K w ⊓ (cylinderValue x w.1 ⊓ cylinderValue y w.2)) hxy
  let E : Fin n → Word := fun _ => []
  have hE : a ≤ stemCylinder stem E := by rw [show stemCylinder stem E = ⊤ from stemCylinder_empty_r143 stem]; exact le_top
  have haX : a ≤ cylinderValue x uv.1 := haBoxes.trans (inf_le_right.trans inf_le_left)
  have haY : a ≤ cylinderValue y uv.2 := haBoxes.trans (inf_le_right.trans inf_le_right)
  have hHit := weightedCluster_given_boxes_r143 K S stem x E uv.1 (hap.trans hx) hE haX
  obtain ⟨j,b,hb,hba,hbFirst⟩ := exists_nonzero_below_choice_r135 a ha
    (fun k => ((S k).weight ⊓ matchedValue K stem (S k).stem) ⊓
      (stemCylinder (S k).stem E ⊓ cylinderValue (S k).tip uv.1)) hHit
  have hbWeight : b ≤ (S j).weight := hbFirst.trans (inf_le_left.trans inf_le_left)
  have hbMat : b ≤ matchedValue K stem (S j).stem := hbFirst.trans (inf_le_left.trans inf_le_right)
  have hRev : b ≤ matchedValue K (S j).stem stem := by
    apply le_iInf
    intro i
    exact (le_inf hbWeight (hbMat.trans (iInf_le _ i))).trans (reverse j i)
  obtain ⟨W,c,hc,hcb,hcW⟩ := exists_matchedWordPairs_r147 K (S j).stem stem b hb hRev
  let V (i : Fin n) := (W i).2
  have hcStem : c ≤ stemCylinder stem V := le_iInf (fun i => (hcW i).2.2)
  have hCy : c ≤ weightedCluster K S stem y := hcb.trans (hba.trans (hap.trans hy))
  have hCw : c ≤ cylinderValue y uv.2 := hcb.trans (hba.trans haY)
  obtain ⟨k,q,hq,hqc,hqSecond⟩ := exists_nonzero_below_choice_r135 c hc
    (fun k => ((S k).weight ⊓ matchedValue K stem (S k).stem) ⊓
      (stemCylinder (S k).stem V ⊓ cylinderValue (S k).tip uv.2))
    (weightedCluster_given_boxes_r143 K S stem y V uv.2 hCy hcStem hCw)
  have hqb := hqc.trans hcb
  have hqa := hqb.trans hba
  have hqStem : q ≤ stemCylinder (S k).stem V := hqSecond.trans (inf_le_right.trans inf_le_left)
  have hqMat : q ≤ matchedValue K (S j).stem (S k).stem :=
    matchedValue_of_wordPairs_r147 K (S j).stem (S k).stem W
      (fun i => ⟨hqc.trans (hcW i).1,hqc.trans (hcW i).2.1,hqStem.trans (iInf_le _ i)⟩)
  have hqTipEdge : q ≤ colorValue K (S j).tip (S k).tip :=
    edgeBox_suffices_r136 K (S j).tip (S k).tip uv (hqa.trans (haBoxes.trans inf_le_left))
      (hqb.trans (hbFirst.trans (inf_le_right.trans inf_le_right)))
      (hqSecond.trans (inf_le_right.trans inf_le_right))
  exact ⟨j,k,q,hq,hqa.trans hap,hqb.trans hbWeight,
    hqSecond.trans (inf_le_left.trans inf_le_left),hqMat,hqTipEdge⟩

end CantorCodes
end JSP000933
