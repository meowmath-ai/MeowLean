import JSP000933RelativeMixedReals
import JSP000933BooleanAvoidanceSchedule

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def tableAgreement {I : Type} (u v : I→B) : B :=
  ⨅ i,bitEq (u i) (v i)

theorem tableAgreement_spec_r441 {I : Type} (u v : I→B) (m : B) :
    m≤tableAgreement u v ↔ ∀ i,m⊓u i=m⊓v i := by
  constructor
  · intro h i
    exact (le_bitEq_iff_r126 _ _ _).mp (h.trans (iInf_le _ i))
  · intro h
    exact le_iInf (fun i => (le_bitEq_iff_r126 _ _ _).mpr (h i))

def restrictEncoded {I : Type} [Encodable I] (r : ℕ→B) (i : I) : B :=
  r (Encodable.encode i)

noncomputable def extendEncoded {I : Type} [Encodable I] (u : I→B) : ℕ→B :=
  fun n => match (Encodable.decode n : Option I) with
    | some i => u i
    | none => ⊥

theorem mixedCH_codeCover_r441 {I : Type} [Encodable I]
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e) (u : I→B) :
    (⨆ j,tableAgreement u (restrictEncoded (e j)))=⊤ := by
  apply top_unique
  rw [← hE (extendEncoded u)]
  apply iSup_le
  intro j
  apply le_iSup_of_le j
  apply (tableAgreement_spec_r441 _ _ _).mpr
  intro i
  have h := (le_realEqValue_iff_r126 _ _ _).mp
    (le_rfl : realEqValue (extendEncoded u) (e j)≤realEqValue (extendEncoded u) (e j))
  simpa only [restrictEncoded,extendEncoded,Encodable.encodek] using h (Encodable.encode i)

def sampleTable {n : ℕ} (u : ℕ→BooleanSample B n) : ℕ×SampleSlot n→B :=
  fun q => sampleValues (u q.1) q.2

def decodeRelativeSamples {n : ℕ} (u : ℕ×SampleSlot n→B) : ℕ→BooleanSample B n :=
  fun j => ⟨fun i k => u (j,.inl (i,k)),fun k => u (j,.inr (.inl k)),u (j,.inr (.inr ()))⟩

theorem sampleTable_decode_r441 {n : ℕ} (u : ℕ×SampleSlot n→B) :
    sampleTable (decodeRelativeSamples u)=u := by
  funext q
  rcases q with ⟨j,q⟩
  cases q with
  | inl ik => rfl
  | inr rest => cases rest <;> rfl

structure RelativeAvoidanceSchedule (B : Type) where
  closedCode : OmegaOneIndex→Word→B
  sampleCode : (n : ℕ)→OmegaOneIndex→ℕ→BooleanSample B n

noncomputable def relativeScheduleFromEnum (e : OmegaOneIndex→ℕ→B) : RelativeAvoidanceSchedule B :=
  ⟨fun j => restrictEncoded (e j),fun _ j => decodeRelativeSamples (restrictEncoded (e j))⟩

theorem relativeClosedCodes_cover_r441 (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (u : Word→B) :
    (⨆ j,tableAgreement u ((relativeScheduleFromEnum e).closedCode j))=⊤ :=
  mixedCH_codeCover_r441 e hE u

theorem relativeSampleCodes_cover_r441 (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    {n : ℕ} (u : ℕ→BooleanSample B n) :
    (⨆ j,tableAgreement (sampleTable u) (sampleTable ((relativeScheduleFromEnum e).sampleCode n j)))=⊤ := by
  simp only [relativeScheduleFromEnum,sampleTable_decode_r441]
  exact mixedCH_codeCover_r441 e hE (sampleTable u)

end RelativeOCA
end JSP000933
