import JSP000930NegativeReindexedAmbientAntichain

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes

variable {B I N : Type} [CompleteBooleanAlgebra B]

noncomputable def placementCut (E : MixedEnumeration OmegaOneIndex I B)
    (W : ℕ → I → B) (a : OmegaOneIndex) : B :=
  ⨅ n : ℕ,⨆ b : {s : OmegaOneIndex // s < a},(aboveValue (placementRow E (W n)) b.val)ᶜ

theorem placementCuts_cover (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q)
    (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : ℕ → I → B)
    (hV : ∀ n j,W n j ≤ Q.valid (f j))
    (hW : ∀ n j k,j ≠ k → (W n j ⊓ W n k) ⊓ commonRefinementValue Q (f j) (f k) = ⊥) :
    (⨆ a,placementCut E W a) = ⊤ := by
  let V (n : ℕ) (b : OmegaOneIndex) := (aboveValue (placementRow E (W n)) b)ᶜ
  have hV' (n : ℕ) : (⨆ b,V n b) = ⊤ := by
    have he := congrArg (fun p : B => pᶜ)
      (placed_rows_are_bounded Q hQ E f (W n) (hV n) (hW n))
    simpa only [unboundedValue,compl_iInf,compl_bot,V] using he
  exact top_unique ((le_iInf (fun n => (hV' n).ge)).trans (hB V))

theorem placementCut_kills_late (E : MixedEnumeration OmegaOneIndex I B)
    (W : ℕ → I → B) (a r : OmegaOneIndex) (hr : a ≤ r) (n : ℕ) :
    Disjoint (placementCut E W a) (placementRow E (W n) r) := by
  apply le_compl_iff_disjoint_right.mp
  apply (iInf_le _ n).trans
  apply iSup_le
  intro b
  exact compl_le_compl (le_iSup
    (fun j : {s : OmegaOneIndex // b.val < s} => placementRow E (W n) j.val)
    ⟨r,b.property.trans_le hr⟩)

theorem traceRectangle_iSup (Q : ValuedPoset B N) (t : N) {J : Type} (W : J → B) :
    traceRectangle Q t (⨆ j,W j) = ⨆ j,traceRectangle Q t (W j) := by
  simp only [traceRectangle,baseEmbed_joins_r427,iSup_inf_eq]

noncomputable def placementTableReal (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (a : OmegaOneIndex)
    (T : CutCodeSlot a → B) : ℕ → TotalBA Q :=
  fun n => ⨆ r : {s : OmegaOneIndex // s < a},⨆ j : I,
    traceRectangle Q (f j) (T (n,r) ⊓ firstTracePlacement E r.val j)

theorem split_trace_column (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N)
    (W : I → B) (j : I) :
    traceRectangle Q (f j) (W j) = ⨆ r,traceRectangle Q (f j) (placementWeight E W r j) := by
  rw [← traceRectangle_iSup,placementWeight_column_cover]

theorem placement_truncated_value (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : ℕ → I → B)
    (a : OmegaOneIndex) (m : B) (hm : m ≤ placementCut E W a) (n : ℕ) :
    let S := fun p : CutCodeSlot a => placementRow E (W p.1) p.2.val
    baseEmbed Q m ⊓ (⨆ j,traceRectangle Q (f j) (W n j)) =
      baseEmbed Q m ⊓ placementTableReal Q E f a S n := by
  classical
  let S := fun p : CutCodeSlot a => placementRow E (W p.1) p.2.val
  change _ = baseEmbed Q m ⊓ placementTableReal Q E f a S n
  unfold placementTableReal
  simp only [S,← placementWeight_split]
  simp only [split_trace_column Q E f (W n),inf_iSup_eq]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro r
    by_cases hr : r < a
    · exact le_iSup_of_le ⟨r,hr⟩ (le_iSup (fun k => baseEmbed Q m ⊓
      traceRectangle Q (f k) (placementWeight E (W n) r k)) j)
    · have HD := ((placementCut_kills_late E W a r (le_of_not_gt hr) n).mono_left hm).mono_right
        (show placementWeight E (W n) r j ≤ placementRow E (W n) r from le_iSup _ j)
      rw [traceRectangle_disjoint_base_r467 Q (f j) HD]
      exact bot_le
  · apply iSup_le
    intro r
    apply iSup_le
    intro j
    exact le_iSup_of_le j (le_iSup (fun s => baseEmbed Q m ⊓
      traceRectangle Q (f j) (placementWeight E (W n) s j)) r.val)

theorem placementTableReal_mask (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (a : OmegaOneIndex)
    (u v : CutCodeSlot a → B) (m : B) (he : m ≤ tableAgreement u v) (n : ℕ) :
    baseEmbed Q m ⊓ placementTableReal Q E f a u n =
      baseEmbed Q m ⊓ placementTableReal Q E f a v n := by
  have h := (tableAgreement_spec_r441 u v m).mp he
  unfold placementTableReal
  apply mask_iSup_congr_r126
  intro r
  apply mask_iSup_congr_r126
  intro j
  rw [traceRectangle_meet_base_r467,traceRectangle_meet_base_r467]
  exact congrArg (traceRectangle Q (f j))
    ((inf_assoc _ _ _).symm.trans ((congrArg (fun x => x ⊓ firstTracePlacement E r.val j)
      (h (n,r))).trans (inf_assoc _ _ _)))

end JSP000930.Negative
