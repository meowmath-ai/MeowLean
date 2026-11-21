import JSP000930PositiveFiniteCertificateSoundnessInFullAlgebra
import JSP000930PositiveLocalizedFreshPairActualPrefix

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000930.Positive.Dyadic JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem finite_boxes_mask_map (F : CompleteValueMap B C) {N : ℕ}
    (W : TaylorFinBoxes N) (A : ℕ → ComplexBits B) :
    F.toFun (W.mask A) = W.mask (fun n => mapComplexBits F (A n)) := by
  unfold TaylorFinBoxes.mask
  rw [F.map_iInf]
  apply iInf_congr
  intro j
  rcases j with ⟨i,b⟩
  cases b <;> simp [TaylorCoordinateBox.value,cutSide,mapComplexBits,F.map_inf,F.map_compl]

theorem FreshTaylorCertificate.value_map (F : CompleteValueMap B C) {ab : ℚ × ℚ}
    (K : FreshTaylorCertificate ab) (U V : TaylorSlot → B) :
    F.toFun (K.value U V) = K.value (fun j => F.toFun (U j)) (fun j => F.toFun (V j)) := by
  simp only [FreshTaylorCertificate.value,F.map_inf,finite_boxes_mask_map,
    F.map_iInf,radiusBudgetBits_map,mapComplexBits_coeff]

noncomputable def earlierCertificateUnion
    (U V : TaylorSlot → B) (m : B) (ab : ℚ × ℚ) : B :=
  ⨆ K : FreshTaylorCertificate ab,m ⊓ K.value U V

theorem earlierCertificateUnion_dense
    (U V : TaylorSlot → B) (m : B) (w : List Bool)
    (hG : m ≤ validDistinctTaylorPair U V ⊓
      (growthValue (complexCoeffBits U) ⊓ growthValue (complexCoeffBits V))) :
    m ≤ ⨆ ab : {ab : ℚ × ℚ // ProperSubinterval w ab},earlierCertificateUnion U V m ab.val := by
  let s := ⨆ ab : {ab : ℚ × ℚ // ProperSubinterval w ab},earlierCertificateUnion U V m ab.val
  change m ≤ s
  by_contra hn
  let p := m ⊓ sᶜ
  have hp : p ≠ ⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨ab,K,d,hAB,hd,hdp,hK⟩ :=
    exists_freshTaylorCertificate U V w p hp (inf_le_left.trans hG)
  have hds : d ≤ s := le_iSup_of_le ⟨ab,hAB⟩
    (le_iSup_of_le K (le_inf (hdp.trans inf_le_left) hK))
  exact hd (disjoint_compl_right.out _ hds (hdp.trans inf_le_right))

end JSP000930.Positive.Cohen
