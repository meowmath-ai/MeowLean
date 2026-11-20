import JSP000933PreparedProbeBook

namespace JSP000933
namespace ForcingTransport

open OpenGraphForcing CantorCodes

variable {B : Type} [Bot B]

abbrev ProbeWitnessPlan (B : Type) := ProbeIndex→OmegaOneIndex→Bool→(ℕ→B)×B

open scoped Classical in
noncomputable def indexedProbeWitness (W : ProbeWitnessPlan B) (i : ProbeIndex) : (ℕ→B)×B :=
  if h : ∃ j,preparedProbeWitnessCode j=i then
    let j := Classical.choose h
    W j.1 j.2.1 j.2.2
  else (fun _ => ⊥,⊥)

noncomputable def probeWitnessBits (W : ProbeWitnessPlan B) (i : ProbeIndex) : ℕ→B :=
  (indexedProbeWitness W i).1

noncomputable def probeWitnessMember (W : ProbeWitnessPlan B) (i : ProbeIndex) : B :=
  (indexedProbeWitness W i).2

theorem indexedProbeWitness_at_r496 (W : ProbeWitnessPlan B)
    (a : ProbeIndex) (j : OmegaOneIndex) (s : Bool) :
    indexedProbeWitness W (preparedProbeWitnessIndex a j s)=W a j s := by
  classical
  have h : ∃ k,preparedProbeWitnessCode k=preparedProbeWitnessIndex a j s := ⟨(a,j,s),rfl⟩
  have hA : Classical.choose h=(a,j,s) :=
    preparedProbeWitnessCode.injective (Classical.choose_spec h)
  simp only [indexedProbeWitness,dite_eq_left h,hA]

theorem probeWitnessBits_at_r496 (W : ProbeWitnessPlan B)
    (a : ProbeIndex) (j : OmegaOneIndex) (s : Bool) :
    probeWitnessBits W (preparedProbeWitnessIndex a j s)=(W a j s).1 :=
  congrArg Prod.fst (indexedProbeWitness_at_r496 W a j s)

theorem probeWitnessMember_at_r496 (W : ProbeWitnessPlan B)
    (a : ProbeIndex) (j : OmegaOneIndex) (s : Bool) :
    probeWitnessMember W (preparedProbeWitnessIndex a j s)=(W a j s).2 :=
  congrArg Prod.snd (indexedProbeWitness_at_r496 W a j s)

end ForcingTransport
end JSP000933
