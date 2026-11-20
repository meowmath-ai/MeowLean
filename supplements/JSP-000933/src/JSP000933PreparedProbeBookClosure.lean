import JSP000933PreparedProbeBook
import JSP000933ActualReflectedProbesAbsorbing

open Cardinal

namespace JSP000933
namespace ForcingTransport

open PreparedModel OpenGraphForcing CantorCodes RelativeOCA

abbrev ProbeRootField := (Word×Word) ⊕ Unit
abbrev ProbePointField := ℕ ⊕ Unit
abbrev ProbeWitnessField := (OmegaOneIndex×Bool) × (Unit ⊕ ProbePointField)
abbrev ProbeStageField := ProbeRootField ⊕ (ProbePointField ⊕ ProbeWitnessField)

private theorem probeRootField_card_r495 : Cardinal.mk ProbeRootField≤𝔠 := by
  change Cardinal.mk ((Word×Word) ⊕ Unit)≤𝔠
  rw [Cardinal.mk_sum]
  simp only [Cardinal.lift_id]
  exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)

private theorem probePointField_card_r495 : Cardinal.mk ProbePointField≤𝔠 := by
  change Cardinal.mk (ℕ ⊕ Unit)≤𝔠
  rw [Cardinal.mk_sum]
  simp only [Cardinal.lift_id]
  exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)

private theorem probeWitnessField_card_r495 : Cardinal.mk ProbeWitnessField≤𝔠 := by
  have hL : Cardinal.mk (OmegaOneIndex×Bool)≤𝔠 := by
    simp only [Cardinal.mk_prod,Cardinal.lift_id,mk_OmegaOneIndex_r61]
    exact Cardinal.mul_le_of_le Cardinal.aleph0_le_continuum Cardinal.aleph_one_le_continuum
      (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have hR : Cardinal.mk (Unit ⊕ ProbePointField)≤𝔠 := by
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id]
    exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum
      (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum) probePointField_card_r495
  change Cardinal.mk ((OmegaOneIndex×Bool)×(Unit ⊕ ProbePointField))≤𝔠
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  exact Cardinal.mul_le_of_le Cardinal.aleph0_le_continuum hL hR

theorem probeStageField_card_r495 : Cardinal.mk ProbeStageField<GroundContinuumSucc := by
  suffices h : Cardinal.mk ProbeStageField≤𝔠 from h.trans_lt (Order.lt_succ _)
  change Cardinal.mk (ProbeRootField ⊕ (ProbePointField ⊕ ProbeWitnessField))≤𝔠
  rw [Cardinal.mk_sum ProbeRootField (ProbePointField ⊕ ProbeWitnessField),
    Cardinal.mk_sum ProbePointField ProbeWitnessField]
  simp only [Cardinal.lift_id]
  exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum probeRootField_card_r495
    (Cardinal.add_le_of_le Cardinal.aleph0_le_continuum probePointField_card_r495
      probeWitnessField_card_r495)

noncomputable def probePointFieldIndex (a : ProbeIndex) : ProbePointField→ProbeIndex
  | .inl n => preparedProbeBook.pointBit a n
  | .inr _ => preparedProbeBook.pointMember a

noncomputable def probeStageFieldIndex (a : ProbeIndex) : ProbeStageField→ProbeIndex
  | .inl (.inl w) => preparedProbeBook.graphBit w
  | .inl (.inr _) => preparedProbeBook.badMark
  | .inr (.inl k) => probePointFieldIndex a k
  | .inr (.inr (⟨j,s⟩,.inl _)) => preparedProbeWitnessIndex a j s
  | .inr (.inr (⟨j,s⟩,.inr k)) => probePointFieldIndex (preparedProbeWitnessIndex a j s) k

noncomputable def preparedProbeClosureBound (a : ProbeIndex) : ProbeIndex :=
  Classical.choose (continuumSuccIndex_family_bounded_r399 (probeStageFieldIndex a) probeStageField_card_r495)

theorem preparedProbeClosureBound_spec_r495 (a : ProbeIndex) :
    preparedProbeBook.badMark<preparedProbeClosureBound a ∧
    (∀ w,preparedProbeBook.graphBit w<preparedProbeClosureBound a) ∧
    preparedProbeBook.pointMember a<preparedProbeClosureBound a ∧
    (∀ n,preparedProbeBook.pointBit a n<preparedProbeClosureBound a) ∧
    ∀ j s,
      preparedProbeWitnessIndex a j s<preparedProbeClosureBound a ∧
      preparedProbeBook.pointMember (preparedProbeWitnessIndex a j s)<preparedProbeClosureBound a ∧
      ∀ n,preparedProbeBook.pointBit (preparedProbeWitnessIndex a j s) n<preparedProbeClosureBound a := by
  have h := Classical.choose_spec
    (continuumSuccIndex_family_bounded_r399 (probeStageFieldIndex a) probeStageField_card_r495)
  exact ⟨h (.inl (.inr ())),fun w => h (.inl (.inl w)),
    h (.inr (.inl (.inr ()))),fun n => h (.inr (.inl (.inl n))),
    fun j s => ⟨h (.inr (.inr ((j,s),.inl ()))),
      h (.inr (.inr ((j,s),.inr (.inr ())))),
      fun n => h (.inr (.inr ((j,s),.inr (.inl n))))⟩⟩

theorem earlyPreparedProbes_below_r495 {d : ProbeIndex}
    (h : ∀ a<d,preparedProbeClosureBound a<d) (a : ProbeIndex) (ha : a<d) :
    preparedProbeBook.badMark<d ∧
    (∀ w,preparedProbeBook.graphBit w<d) ∧
    preparedProbeBook.pointMember a<d ∧
    (∀ n,preparedProbeBook.pointBit a n<d) ∧
    ∀ j s,preparedProbeWitnessIndex a j s<d ∧
      preparedProbeBook.pointMember (preparedProbeWitnessIndex a j s)<d ∧
      ∀ n,preparedProbeBook.pointBit (preparedProbeWitnessIndex a j s) n<d := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := preparedProbeClosureBound_spec_r495 a
  have hb := h a ha
  refine ⟨h1.trans hb,fun w => (h2 w).trans hb,h3.trans hb,fun n => (h4 n).trans hb,fun j s => ?_⟩
  obtain ⟨hj,hM,hB⟩ := h5 j s
  exact ⟨hj.trans hb,hM.trans hb,fun n => (hB n).trans hb⟩

end ForcingTransport
end JSP000933
