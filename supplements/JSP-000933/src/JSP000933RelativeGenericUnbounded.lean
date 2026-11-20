import JSP000933RelativeCountablePigeonhole
import JSP000933RelativeCodeSchedules

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem unboundedValue_zero_r443 : unboundedValue (fun _ : OmegaOneIndex => (⊥ : B))=⊥ := by
  apply le_bot_iff.mp
  simpa only [iSup_bot] using
    (unboundedValue_le_some_r431 (fun _ => (⊥ : B)))

theorem unboundedValue_encodablePartition_r443 (hB : BoundsCountableOmegaOneNames B)
    {I : Type} [Encodable I] (w : I→OmegaOneIndex→B) :
    unboundedValue (fun i => ⨆ j,w j i)=⨆ j,unboundedValue (w j) := by
  let W (n : ℕ) (i : OmegaOneIndex) :=
    match (Encodable.decode n : Option I) with
    | none => ⊥
    | some j => w j i
  have h1 (i : OmegaOneIndex) : (⨆ n,W n i)=⨆ j,w j i := by
    apply le_antisymm
    · apply iSup_le
      intro n
      cases hd : (Encodable.decode n : Option I) with
      | none => simp [W,hd]
      | some j => simpa [W,hd] using (le_iSup (fun j => w j i) j)
    · apply iSup_le
      intro j
      apply le_iSup_of_le (Encodable.encode j)
      simp only [W,Encodable.encodek,le_rfl]
  have h2 : (⨆ n,unboundedValue (W n))=⨆ j,unboundedValue (w j) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      cases hd : (Encodable.decode n : Option I) with
      | none => simp [W,hd,unboundedValue_zero_r443]
      | some j => simpa [W,hd] using (le_iSup (fun j => unboundedValue (w j)) j)
    · apply iSup_le
      intro j
      apply le_iSup_of_le (Encodable.encode j)
      simp only [W,Encodable.encodek,le_rfl]
  have he : (fun i => ⨆ n,W n i)=(fun i => ⨆ j,w j i) := funext h1
  rw [← he,unboundedValue_countablePartition_r433 hB W,h2]

theorem unboundedValue_countableTypePartition_r443 (hB : BoundsCountableOmegaOneNames B)
    {I : Type} [Countable I] (w : I→OmegaOneIndex→B) :
    unboundedValue (fun i => ⨆ j,w j i)=⨆ j,unboundedValue (w j) := by
  letI := Encodable.ofCountable I
  exact unboundedValue_encodablePartition_r443 hB w

end RelativeOCA
end JSP000933
