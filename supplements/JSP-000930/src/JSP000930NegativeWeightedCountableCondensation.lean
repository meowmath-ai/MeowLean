import JSP000930NegativeRealPreparedRelativeDirectLimitCCC

namespace JSP000930.Negative

open JSP000933.OpenGraphForcing JSP000933.RelativeOCA
  JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B : Type} [CompleteBooleanAlgebra B]

theorem unboundedValue_countable_cells
    (hB : BoundsCountableOmegaOneNames B) (U : ℕ → OmegaOneIndex → B) :
    unboundedValue (fun i => ⨆ k,U k i) = ⨆ k,unboundedValue (U k) := by
  apply le_antisymm ?_ (iSup_le fun k =>
    unboundedValue_mono_r431 (fun i => le_iSup (fun k => U k i) k))
  apply disjoint_compl_right_iff.mp
  apply disjoint_iff_inf_le.mpr
  let Y := unboundedValue (fun i => ⨆ k,U k i)
  let X := ⨆ k,unboundedValue (U k)
  let m := Y ⊓ Xᶜ
  let F (k : ℕ) (a : OmegaOneIndex) := (aboveValue (U k) a)ᶜ
  let C (b : OmegaOneIndex) := ⨅ k,⨆ a : {a : OmegaOneIndex // a < b},F k a.val
  change m ≤ ⊥
  have hCut : m ≤ ⨆ b,C b := by
    apply (le_iInf ?_).trans (hB F)
    intro k
    have hX : m ≤ (unboundedValue (U k))ᶜ :=
      inf_le_right.trans (compl_le_compl (le_iSup (fun k => unboundedValue (U k)) k))
    simpa only [unboundedValue,compl_iInf,F] using hX
  apply (le_inf le_rfl hCut).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro b
  have hbelow : m ⊓ C b ≤ aboveValue (fun i => ⨆ k,U k i) b :=
    inf_le_left.trans (inf_le_left.trans (iInf_le _ b))
  have hNone (k : ℕ) : C b ≤ (aboveValue (U k) b)ᶜ := by
    apply (iInf_le _ k).trans
    apply iSup_le
    intro a
    exact compl_le_compl (aboveValue_antitone_r431 (U k) a.property.le)
  apply (le_inf le_rfl hbelow).trans
  unfold aboveValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  rw [inf_iSup_eq]
  apply iSup_le
  intro k
  exact (le_inf (inf_le_left.trans (inf_le_right.trans (hNone k)))
    (inf_le_right.trans (le_iSup
      (fun j : {j : OmegaOneIndex // b < j} => U k j.val) j))).trans_eq (compl_inf_eq_bot (a := aboveValue (U k) b))

end JSP000930.Negative
