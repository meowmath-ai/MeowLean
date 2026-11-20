import JSP000933RelativeCardCCC
import JSP000933RelativeMixedCluster

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem unboundedValue_meetConst_r456 (m : B) (w : OmegaOneIndex→B) :
    unboundedValue (fun i => m⊓w i)=m⊓unboundedValue w := by
  have hA (b : OmegaOneIndex) : aboveValue (fun i => m⊓w i) b=m⊓aboveValue w b := by
    unfold aboveValue
    exact (inf_iSup_eq _ _).symm
  apply le_antisymm
  · apply le_inf
    · have hN : Nonempty OmegaOneIndex :=
        Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
      obtain ⟨b⟩ := hN
      exact ((iInf_le _ b).trans_eq (hA b)).trans inf_le_left
    · exact unboundedValue_mono_r431 (fun _ => inf_le_right)
  · apply le_iInf
    intro b
    rw [hA]
    exact inf_le_inf le_rfl (iInf_le _ b)

theorem rowLabelWeight_meetConst_r456 (m : B) (W : OmegaOneIndex→Finset OmegaOneIndex→B) :
    rowLabelWeight (fun i s => m⊓W i s)=(fun i => m⊓rowLabelWeight W i) := by
  funext i
  unfold rowLabelWeight
  exact (inf_iSup_eq _ _).symm

abbrev ClusterBox (n : ℕ) := (Fin n→Word)×Word

noncomputable def failureBoxWeight {n : ℕ} (K : Word×Word→B)
    (F : LabelCandidate→BooleanSample B n)
    (T : OmegaOneIndex→Finset OmegaOneIndex→B) (c : ClusterBox n)
    (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : B :=
  (T i s⊓(stemCylinder (F (i,s)).stem c.1⊓cylinderValue (F (i,s)).tip c.2))⊓
    (weightedClusterHit K F (F (i,s)).stem c.1 c.2)ᶜ

theorem failureBoxWeight_covers_r456 {n : ℕ} (K : Word×Word→B)
    (F : LabelCandidate→BooleanSample B n)
    (T : OmegaOneIndex→Finset OmegaOneIndex→B) (i : OmegaOneIndex) (s : Finset OmegaOneIndex)
    (hFail : T i s⊓weightedCluster K F (F (i,s)).stem (F (i,s)).tip=⊥) :
    T i s=⨆ c : ClusterBox n,failureBoxWeight K F T c i s := by
  have hD : T i s≤(weightedCluster K F (F (i,s)).stem (F (i,s)).tip)ᶜ :=
    le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hFail.le)
  have hE : T i s=T i s⊓(weightedCluster K F (F (i,s)).stem (F (i,s)).tip)ᶜ :=
    (inf_eq_left.mpr hD).symm
  apply le_antisymm
  · rw [hE,weightedCluster_compl_r143,inf_iSup_eq]
    apply iSup_le
    intro U
    rw [inf_iSup_eq]
    apply iSup_le
    intro V
    apply le_iSup_of_le (U,V)
    unfold failureBoxWeight
    exact (inf_assoc _ _ _).symm.le
  · exact iSup_le (fun _ => inf_le_left.trans inf_le_left)

theorem failureBoxWeight_unbounded_r456 {n : ℕ} (hB : BoundsCountableOmegaOneNames B)
    (K : Word×Word→B) (F : LabelCandidate→BooleanSample B n)
    (T : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hFail : ∀ i s,T i s⊓weightedCluster K F (F (i,s)).stem (F (i,s)).tip=⊥) :
    unboundedValue (rowLabelWeight T)=
      ⨆ c : ClusterBox n,unboundedValue (rowLabelWeight (failureBoxWeight K F T c)) := by
  have hRow : rowLabelWeight T=(fun i => ⨆ c : ClusterBox n,
      rowLabelWeight (failureBoxWeight K F T c) i) := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro s
      apply (failureBoxWeight_covers_r456 K F T i s (hFail i s)).le.trans
      apply iSup_le
      intro c
      exact le_iSup_of_le c (le_iSup _ s)
    · apply iSup_le
      intro c
      apply iSup_le
      intro s
      exact inf_le_left.trans (inf_le_left.trans (le_iSup _ s))
  rw [hRow,unboundedValue_countableTypePartition_r443 hB]

end RelativeOCA
end JSP000933
