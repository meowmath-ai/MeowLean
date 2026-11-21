import JSP000930NegativeTracePlacement

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA

variable {B I N : Type} [CompleteBooleanAlgebra B]

noncomputable def placedAmbientWeight (E : MixedEnumeration OmegaOneIndex I B)
    (f : I → N) (W : I → B) (r : OmegaOneIndex) (n : N) : B :=
  ⨆ j : I,⨆ (_ : f j = n),placementWeight E W r j

theorem placedAmbientWeight_row (E : MixedEnumeration OmegaOneIndex I B)
    (f : I → N) (W : I → B) (r : OmegaOneIndex) :
    (⨆ n,placedAmbientWeight E f W r n) = placementRow E W r := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro j
    exact iSup_le fun _ => le_iSup (placementWeight E W r) j
  · apply iSup_le
    intro j
    exact le_iSup_of_le (f j) (le_iSup_of_le j (le_iSup (fun _ : f j = f j =>
      placementWeight E W r j) rfl))

theorem placedAmbientWeight_valid (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : I → B)
    (hW : ∀ j,W j ≤ Q.valid (f j)) (r : OmegaOneIndex) (n : N) :
    placedAmbientWeight E f W r n ≤ Q.valid n := by
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact inf_le_left.trans ((hW j).trans_eq (congrArg Q.valid hj))

theorem placedAmbientWeight_apart (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : I → B)
    (hW : ∀ j k,j ≠ k → (W j ⊓ W k) ⊓ commonRefinementValue Q (f j) (f k) = ⊥)
    (r s : OmegaOneIndex) (hrs : r < s) (n m : N) :
    (placedAmbientWeight E f W r n ⊓ placedAmbientWeight E f W s m) ⊓
      commonRefinementValue Q n m = ⊥ := by
  apply le_bot_iff.mp
  unfold placedAmbientWeight
  rw [iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  rintro ⟨i,j⟩
  rw [iSup_inf_eq,iSup_inf_eq]
  apply iSup_le
  intro hi
  rw [inf_iSup_eq,iSup_inf_eq]
  apply iSup_le
  intro hj
  subst n
  subst m
  by_cases h : i = j
  · subst j
    exact (inf_le_left.trans (inf_le_inf (show placementWeight E W r i ≤
      firstTracePlacement E r i from inf_le_right)
      (show placementWeight E W s i ≤ firstTracePlacement E s i from inf_le_right))).trans
      (disjoint_iff_inf_le.mp (show Disjoint (firstTracePlacement E r i)
        (firstTracePlacement E s i) from firstTracePlacement_colsApart E hrs i))
  · exact (inf_le_inf (inf_le_inf (show placementWeight E W r i ≤ W i from inf_le_left)
      (show placementWeight E W s j ≤ W j from inf_le_left)) le_rfl).trans_eq (hW i j h)

theorem placed_rows_are_bounded (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : I → B)
    (hV : ∀ j,W j ≤ Q.valid (f j))
    (hW : ∀ j k,j ≠ k → (W j ⊓ W k) ⊓ commonRefinementValue Q (f j) (f k) = ⊥) :
    unboundedValue (placementRow E W) = ⊥ := by
  have h := hQ (placedAmbientWeight E f W)
    (placedAmbientWeight_valid Q E f W hV) (placedAmbientWeight_apart Q E f W hW)
  simpa only [placedAmbientWeight_row] using h

end JSP000930.Negative
