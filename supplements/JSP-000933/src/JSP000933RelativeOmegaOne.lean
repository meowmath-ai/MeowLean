import JSP000933MarkedCompatiblePairs
import JSP000933CCCSchedule

namespace JSP000933
namespace RelativeOCA

open Cardinal OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def BoundsCountableOmegaOneNames (B : Type) [CompleteBooleanAlgebra B] : Prop :=
  ∀ V : ℕ→OmegaOneIndex→B,
    (⨅ n,⨆ j,V n j)≤⨆ b : OmegaOneIndex,⨅ n,⨆ j : {j : OmegaOneIndex // j<b},V n j.val

noncomputable def aboveValue (w : OmegaOneIndex→B) (b : OmegaOneIndex) : B :=
  ⨆ j : {j : OmegaOneIndex // b<j},w j.val

noncomputable def unboundedValue (w : OmegaOneIndex→B) : B :=
  ⨅ b : OmegaOneIndex,aboveValue w b

theorem aboveValue_antitone_r431 (w : OmegaOneIndex→B) : Antitone (aboveValue w) := by
  intro a b hab
  apply iSup_le
  intro j
  exact le_iSup (fun k : {k : OmegaOneIndex // a < k} => w k.val) ⟨j.val,hab.trans_lt j.property⟩

theorem unboundedValue_mono_r431 {u v : OmegaOneIndex→B} (h : ∀ i,u i≤v i) :
    unboundedValue u≤unboundedValue v := by
  apply le_iInf
  intro b
  exact (iInf_le _ b).trans (iSup_le (fun j => le_iSup_of_le j (h j.val)))

theorem unboundedValue_le_some_r431 (w : OmegaOneIndex→B) :
    unboundedValue w≤⨆ i,w i := by
  have h0 : Nonempty OmegaOneIndex :=
    Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
  obtain ⟨b⟩ := h0
  exact (iInf_le _ b).trans (iSup_le (fun i => le_iSup w i.val))

theorem unboundedValue_le_pairOverlap_r431 (w : OmegaOneIndex→B) :
    unboundedValue w≤⨆ i : OmegaOneIndex,⨆ j : {j : OmegaOneIndex // i<j},w i⊓w j.val := by
  let u := unboundedValue w
  apply (le_inf le_rfl (unboundedValue_le_some_r431 w)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have h : u⊓w i≤w i⊓aboveValue w i :=
    le_inf inf_le_right (inf_le_left.trans (iInf_le _ i))
  exact h.trans_eq (inf_iSup_eq _ _)

end RelativeOCA
end JSP000933
