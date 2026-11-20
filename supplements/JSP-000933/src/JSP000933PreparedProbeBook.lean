import JSP000933PreparedTypedDiamondDecoder
import JSP000933ActualRawTailCardinality

open Cardinal

namespace JSP000933
namespace ForcingTransport

open PreparedModel OpenGraphForcing CantorCodes

abbrev ProbeIndex := GroundContinuumSuccIndex
abbrev PreparedProbeAtom :=
  (ProbeIndex×ℕ) ⊕ (ProbeIndex ⊕ ((Word×Word) ⊕ Unit))

private theorem aleph0_le_probeIndex_r494 : (ℵ₀ : Cardinal)≤GroundContinuumSucc :=
  Cardinal.aleph0_le_continuum.trans (Order.le_succ _)

theorem preparedProbeAtom_card_r494 : Cardinal.mk PreparedProbeAtom≤GroundContinuumSucc := by
  have h0 := aleph0_le_probeIndex_r494
  have hn : Cardinal.mk ℕ≤GroundContinuumSucc := Cardinal.mk_le_aleph0.trans h0
  have hw : Cardinal.mk (Word×Word)≤GroundContinuumSucc := Cardinal.mk_le_aleph0.trans h0
  have hu : Cardinal.mk Unit≤GroundContinuumSucc := Cardinal.mk_le_aleph0.trans h0
  have hp : Cardinal.mk (ProbeIndex×ℕ)≤GroundContinuumSucc := by
    simp only [Cardinal.mk_prod,Cardinal.lift_id,continuumSuccIndex_card_r406]
    exact Cardinal.mul_le_of_le h0 le_rfl hn
  have hk : Cardinal.mk ProbeIndex≤GroundContinuumSucc := continuumSuccIndex_card_r406.le
  unfold PreparedProbeAtom
  simp only [Cardinal.mk_sum,Cardinal.lift_id]
  exact Cardinal.add_le_of_le h0 hp
    (Cardinal.add_le_of_le h0 hk (Cardinal.add_le_of_le h0 hw hu))

noncomputable def preparedProbeAtomCode : PreparedProbeAtom↪ProbeIndex :=
  Classical.choice ((Cardinal.le_def _ _).mp
    (preparedProbeAtom_card_r494.trans_eq continuumSuccIndex_card_r406.symm))

noncomputable def preparedProbeBook : ProbeBook where
  pointBit i n := preparedProbeAtomCode (.inl (i,n))
  pointMember i := preparedProbeAtomCode (.inr (.inl i))
  graphBit w := preparedProbeAtomCode (.inr (.inr (.inl w)))
  badMark := preparedProbeAtomCode (.inr (.inr (.inr ())))

abbrev ProbeWitnessKey := ProbeIndex×(OmegaOneIndex×Bool)

theorem preparedProbeWitnessKey_card_r494 : Cardinal.mk ProbeWitnessKey≤GroundContinuumSucc := by
  have h0 := aleph0_le_probeIndex_r494
  have hB : Cardinal.mk Bool≤GroundContinuumSucc := Cardinal.mk_le_aleph0.trans h0
  have hO : Cardinal.mk OmegaOneIndex≤GroundContinuumSucc := by
    rw [mk_OmegaOneIndex_r61]
    exact Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)
  unfold ProbeWitnessKey
  simp only [Cardinal.mk_prod,continuumSuccIndex_card_r406,
    Cardinal.lift_id]
  exact Cardinal.mul_le_of_le h0 le_rfl (Cardinal.mul_le_of_le h0 hO hB)

noncomputable def preparedProbeWitnessCode : ProbeWitnessKey↪ProbeIndex :=
  Classical.choice ((Cardinal.le_def _ _).mp
    (preparedProbeWitnessKey_card_r494.trans_eq continuumSuccIndex_card_r406.symm))

noncomputable def preparedProbeWitnessIndex (a : ProbeIndex) (j : OmegaOneIndex) (side : Bool) :
    ProbeIndex := preparedProbeWitnessCode (a,j,side)

theorem preparedProbeWitnessIndex_inj_r494 {a b : ProbeIndex} {j k : OmegaOneIndex} {s t : Bool}
    (h : preparedProbeWitnessIndex a j s=preparedProbeWitnessIndex b k t) :
    a=b ∧ j=k ∧ s=t := by
  have he : (a,j,s)=(b,k,t) := preparedProbeWitnessCode.injective h
  exact ⟨congrArg Prod.fst he,congrArg (fun x : ProbeWitnessKey => x.2.1) he,
    congrArg (fun x : ProbeWitnessKey => x.2.2) he⟩

variable {B : Type} [Bot B]

def ProbeAtomValue
    (X : ProbeIndex→ℕ→B) (M : ProbeIndex→B) (K : Word×Word→B) (p : B) :
    PreparedProbeAtom→B
  | .inl (i,n) => X i n
  | .inr (.inl i) => M i
  | .inr (.inr (.inl w)) => K w
  | .inr (.inr (.inr _)) => p

open scoped Classical in
noncomputable def preparedProbeValues
    (X : ProbeIndex→ℕ→B) (M : ProbeIndex→B) (K : Word×Word→B) (p : B) (i : ProbeIndex) : B :=
  if h : ∃ t,preparedProbeAtomCode t=i then ProbeAtomValue X M K p (Classical.choose h) else ⊥

theorem preparedProbeValues_atom_r494
    (X : ProbeIndex→ℕ→B) (M : ProbeIndex→B) (K : Word×Word→B) (p : B)
    (t : PreparedProbeAtom) :
    preparedProbeValues X M K p (preparedProbeAtomCode t)=ProbeAtomValue X M K p t := by
  classical
  have h : ∃ s,preparedProbeAtomCode s=preparedProbeAtomCode t := ⟨t,rfl⟩
  have ht : Classical.choose h=t := preparedProbeAtomCode.injective (Classical.choose_spec h)
  simp only [preparedProbeValues,dite_eq_left h,ht]

theorem preparedProbeValues_tagEquations_r494
    (X : ProbeIndex→ℕ→B) (M : ProbeIndex→B) (K : Word×Word→B) (p : B) :
    (∀ i n,preparedProbeValues X M K p (preparedProbeBook.pointBit i n)=X i n) ∧
    (∀ i,preparedProbeValues X M K p (preparedProbeBook.pointMember i)=M i) ∧
    (∀ w,preparedProbeValues X M K p (preparedProbeBook.graphBit w)=K w) ∧
    preparedProbeValues X M K p preparedProbeBook.badMark=p :=
  ⟨fun i n => preparedProbeValues_atom_r494 X M K p (.inl (i,n)),
    fun i => preparedProbeValues_atom_r494 X M K p (.inr (.inl i)),
    fun w => preparedProbeValues_atom_r494 X M K p (.inr (.inr (.inl w))),
    preparedProbeValues_atom_r494 X M K p (.inr (.inr (.inr ())))⟩

end ForcingTransport
end JSP000933
