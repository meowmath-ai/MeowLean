import JSP000933RelativeMixedDenseSamples
import JSP000933DensePreservesBooleanClusters

namespace JSP000933
namespace RelativeOCA

open CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem weightedClusterHit_le_of_allBoxes_r452 (K : Word × Word → B) {n : ℕ}
    {J : Type} (F : I → BooleanSample B n) (G : J → BooleanSample B n)
    (dense : ∀ (U : Fin n → List Word) (V : List Word),
      (⨆ i, sampleBox (F i) U V) ≤ ⨆ j, sampleBox (G j) U V)
    (stem : Fin n → ℕ → B) (U : Fin n → Word) (V : Word) :
    weightedClusterHit K F stem U V ≤ weightedClusterHit K G stem U V := by
  classical
  let small := weightedClusterHit K G stem U V
  by_contra h
  let p := weightedClusterHit K F stem U V ⊓ smallᶜ
  have hN : p ≠ ⊥ := by
    intro hb
    apply h
    have hd : Disjoint (weightedClusterHit K F stem U V) smallᶜ :=
      disjoint_iff_inf_le.mpr hb.le
    exact (le_compl_iff_disjoint_right.mpr hd).trans_eq (compl_compl _)
  let term (i : I) := ((F i).weight ⊓ matchedValue K stem (F i).stem) ⊓
    (stemCylinder (F i).stem U ⊓ cylinderValue (F i).tip V)
  obtain ⟨i,q,hq,hqp,hqTerm⟩ := exists_nonzero_below_choice_r135 p hN term inf_le_left
  obtain ⟨W,r,hr,hrq,hrW⟩ := exists_matchedWordPairs_r147 K stem (F i).stem q hq
    (hqTerm.trans (inf_le_left.trans inf_le_right))
  let UU (i : Fin n) := [U i,(W i).2]
  have hR : r ≤ sampleBox (F i) UU [V] := by
    apply le_inf (hrq.trans (hqTerm.trans (inf_le_left.trans inf_le_left)))
    apply le_inf
    · apply le_iInf
      intro j
      change r ≤ cylinderValue ((F i).stem j) (U j) ⊓
        (cylinderValue ((F i).stem j) (W j).2 ⊓ ⊤)
      have hu : r ≤ cylinderValue ((F i).stem j) (U j) :=
        hrq.trans (hqTerm.trans ((inf_le_right.trans inf_le_left).trans (iInf_le _ j)))
      exact le_inf hu (le_inf (hrW j).2.2 le_top)
    · change r ≤ cylinderValue (F i).tip V ⊓ ⊤
      exact le_inf (hrq.trans (hqTerm.trans (inf_le_right.trans inf_le_right))) le_top
  have hBig : r ≤ ⨆ j : J, sampleBox (G j) UU [V] :=
    (hR.trans (le_iSup (fun k => sampleBox (F k) UU [V]) i)).trans (dense UU [V])
  obtain ⟨j,t,ht,htr,htBox⟩ := exists_nonzero_below_choice_r135 r hr
    (fun j : J => sampleBox (G j) UU [V]) hBig
  have htMulti (k : Fin n) :
      t ≤ cylinderValue ((G j).stem k) (U k) ⊓
        (cylinderValue ((G j).stem k) (W k).2 ⊓ ⊤) :=
    htBox.trans ((inf_le_right.trans inf_le_left).trans (iInf_le _ k))
  have hMat : t ≤ matchedValue K stem (G j).stem :=
    matchedValue_of_wordPairs_r147 K stem (G j).stem W
      (fun k => ⟨htr.trans (hrW k).1,htr.trans (hrW k).2.1,
        (htMulti k).trans (inf_le_right.trans inf_le_left)⟩)
  have hTip : t ≤ cylinderValue (G j).tip V :=
    htBox.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have hSmall : t ≤ small :=
    le_iSup_of_le j (le_inf (le_inf (htBox.trans inf_le_left) hMat)
      (le_inf (le_iInf (fun k => (htMulti k).trans inf_le_left)) hTip))
  have hCompl : t ≤ smallᶜ := htr.trans (hrq.trans (hqp.trans inf_le_right))
  exact ht (le_bot_iff.mp ((le_inf hSmall hCompl).trans_eq (inf_compl_eq_bot')))

theorem weightedCluster_eq_of_allBoxes_r452 {J : Type} (K : Word×Word→B) {n : ℕ}
    (F : I→BooleanSample B n) (G : J→BooleanSample B n)
    (dense : ∀ (U : Fin n→List Word) (V : List Word),
      (⨆ i,sampleBox (F i) U V)=(⨆ j,sampleBox (G j) U V))
    (stem : Fin n→ℕ→B) (tip : ℕ→B) :
    weightedCluster K F stem tip=weightedCluster K G stem tip := by
  have hHit (U : Fin n→Word) (V : Word) :
      weightedClusterHit K F stem U V=weightedClusterHit K G stem U V :=
    le_antisymm (weightedClusterHit_le_of_allBoxes_r452 K F G (fun U V => (dense U V).le) stem U V)
      (weightedClusterHit_le_of_allBoxes_r452 K G F (fun U V => (dense U V).ge) stem U V)
  simp only [weightedCluster,hHit]

theorem exists_mixedClusterSequence_r452 (K : Word×Word→B) {n : ℕ}
    (F : I→BooleanSample B n) :
    ∃ G : ℕ→BooleanSample B n,∀ stem x,weightedCluster K F stem x=weightedCluster K G stem x := by
  obtain ⟨G,hG⟩ := exists_countable_mixedWeightedBoxDense_r451 F
  exact ⟨G,weightedCluster_eq_of_allBoxes_r452 K F G (fun U V => (hG U V).symm)⟩

end RelativeOCA
end JSP000933
