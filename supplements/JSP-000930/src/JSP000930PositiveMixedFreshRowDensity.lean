import JSP000930PositiveAppendOutsidePrefix
import JSP000933FiniteBooleanWitnesses

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport
  JSP000933.CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem fresh_row_meets_mixed_dense_words
    (S : Set (I × ℕ)) (i : I) (hFresh : ∀ n, (i,n) ∉ S)
    (p : CohenBlockBA B S) (D : List Bool → CohenBlockBA B S)
    (hD : ∀ u, p ≤ ⨆ v, D (u ++ v)) :
    blockEmbed B S p ≤ ⨆ w, wordValue B i w ⊓ blockEmbed B S (D w) := by
  classical
  let z : CohenBA B (I × ℕ) := ⨆ w, wordValue B i w ⊓ blockEmbed B S (D w)
  change blockEmbed B S p ≤ z
  by_contra hz
  let bad := blockEmbed B S p ⊓ zᶜ
  have hNZ : bad ≠ ⊥ := fun e =>
    hz (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 bad hNZ
  let p₀ := restrictTotal t S
  have h₀ : imageCondition p₀ ≤ p := by
    apply (image_le_iff_member _ _).mpr
    have ht' : t ∈ (blockEmbed B S p : LowerSet (CohenTotal B (I × ℕ))) :=
      (image_le_iff_member _ _).mp (ht.trans inf_le_left)
    exact ht'
  let u := completeRowWord t.trace i
  have hc : imageCondition p₀ ≤ ⨆ v,D (u ++ v) := h₀.trans (hD u)
  obtain ⟨v,d,hd,hd₀,hdv⟩ := exists_nonzero_below_choice_r135 (imageCondition p₀)
    (imageCondition_ne_bot_r50 p₀) (fun v => D (u ++ v)) hc
  obtain ⟨s₀,hs₀⟩ := imageCondition_dense_r50 d hd
  obtain ⟨s,hss,hsp⟩ := exists_joint_of_image_le_r429 (hs₀.trans hd₀)
  obtain ⟨q,hq,hWord,hNoNew⟩ := exists_append_no_new_other_row t.trace i v
  let tq : CohenTotal B (I × ℕ) := ⟨t.mask,q,t.nonzero,le_top⟩
  have htq : tq ≤ t := (cohen_total_le_iff _ _).mpr ⟨le_rfl,hq⟩
  have hr : p₀ ≤ restrictTotal tq S := by
    change p₀.1 ≤ (restrictTotal tq S).1
    exact (cohen_total_le_iff _ _).mpr ⟨le_rfl,
      restriction_unchanged_off_fresh_row hq hNoNew S hFresh⟩
  obtain ⟨w,hwq,hws⟩ := lift_stronger_total_block tq S s (hsp.trans hr)
  have hWordW : imageCondition w ≤ wordValue B i (u ++ v) :=
    (imageCondition_mono_r50 hwq).trans (image_le_wordValue tq i (u ++ v) hWord)
  have hSetW : imageCondition w ≤ blockEmbed B S (D (u ++ v)) := by
    apply (imageCondition_mono_r50 hws).trans
    rw [← blockEmbed_image]
    exact (cohenBlockProjection B S).pull_mono
      ((imageCondition_mono_r50 hss).trans (hs₀.trans hdv))
  have hW : imageCondition w ≤ z := le_iSup_of_le (u ++ v) (le_inf hWordW hSetW)
  have hN : imageCondition w ≤ zᶜ :=
    (imageCondition_mono_r50 (hwq.trans htq)).trans (ht.trans inf_le_right)
  exact imageCondition_ne_bot_r50 w (disjoint_compl_right.out _ hW hN)

end JSP000930.Positive.Cohen
