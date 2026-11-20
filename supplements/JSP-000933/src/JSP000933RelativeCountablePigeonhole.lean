import JSP000933RelativeOmegaOne

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem aboveValue_iSup_r433 {I : Type} (w : I→OmegaOneIndex→B) (a : OmegaOneIndex) :
    aboveValue (fun i => ⨆ n,w n i) a=⨆ n,aboveValue (w n) a := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro n
    exact le_iSup_of_le n (le_iSup (fun j : {j : OmegaOneIndex // a < j} => w n j.val) i)
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup_of_le i (le_iSup (fun k => w k i.val) n)

theorem unboundedValue_countablePartition_r433 (hB : BoundsCountableOmegaOneNames B)
    (w : ℕ→OmegaOneIndex→B) :
    unboundedValue (fun i => ⨆ n,w n i)=⨆ n,unboundedValue (w n) := by
  apply le_antisymm
  · let f (i : OmegaOneIndex) := ⨆ n,w n i
    let a := unboundedValue f
    let b := ⨆ n,unboundedValue (w n)
    change a≤b
    by_contra h
    let m := a⊓bᶜ
    have hM : m≠⊥ := fun he =>
      h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    let V (n : ℕ) (j : OmegaOneIndex) := (aboveValue (w n) j)ᶜ
    have hV (n : ℕ) : m≤⨆ j,V n j := by
      have h' : m≤(unboundedValue (w n))ᶜ :=
        inf_le_right.trans (compl_le_compl (le_iSup (fun k => unboundedValue (w k)) n))
      unfold unboundedValue at h'
      simpa only [compl_iInf,V] using h'
    have hU : m≤⨆ j : OmegaOneIndex,⨅ n,⨆ i : {i : OmegaOneIndex // i<j},V n i.val :=
      (le_iInf hV).trans (hB V)
    have h0 : m≤⊥ := by
      apply (le_inf le_rfl hU).trans
      rw [inf_iSup_eq]
      apply iSup_le
      intro j
      have h1 : m≤aboveValue f j := inf_le_left.trans (iInf_le _ j)
      have h2 : (⨅ n,⨆ i : {i : OmegaOneIndex // i<j},V n i.val)≤(aboveValue f j)ᶜ := by
        unfold f
        rw [aboveValue_iSup_r433,compl_iSup]
        apply le_iInf
        intro n
        apply (iInf_le _ n).trans
        apply iSup_le
        intro i
        exact compl_le_compl (aboveValue_antitone_r431 (w n) i.property.le)
      exact (inf_le_inf h1 h2).trans (disjoint_iff_inf_le.mp (disjoint_compl_right :
        Disjoint (aboveValue f j) (aboveValue f j)ᶜ))
    exact hM (le_bot_iff.mp h0)
  · exact iSup_le (fun n => unboundedValue_mono_r431 (fun i => le_iSup (fun k => w k i) n))

end RelativeOCA
end JSP000933
