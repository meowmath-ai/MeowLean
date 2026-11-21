import JSP000930NegativeCountablePlacementTables

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes

variable {B I N : Type} [CompleteBooleanAlgebra B]

noncomputable def weightedTraceReal (Q : ValuedPoset B N)
    (f : I → N) (W : ℕ → I → B) : ℕ → TotalBA Q :=
  fun n => ⨆ j,traceRectangle Q (f j) (W n j)

theorem placedTraceReal_double_cover (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q)
    (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex I B) (f : I → N) (W : ℕ → I → B)
    (hV : ∀ n j,W n j ≤ Q.valid (f j))
    (hW : ∀ n j k,j ≠ k → (W n j ⊓ W n k) ⊓ commonRefinementValue Q (f j) (f k) = ⊥)
    (e : OmegaOneIndex → ℕ → B) (hE : EnumeratesBooleanReals e) :
    (⨆ a : OmegaOneIndex,⨆ i : OmegaOneIndex,
      realEqValue (weightedTraceReal Q f W) (placementTableReal Q E f a (decodeCutCode a (e i)))) = ⊤ := by
  have hCover : (⨆ a,baseEmbed Q (placementCut E W a)) = ⊤ := by
    rw [← baseEmbed_joins_r427,placementCuts_cover Q hQ hB E f W hV hW,baseEmbed_top_r427]
  apply top_unique
  rw [← hCover]
  apply iSup_le
  intro a
  let u (p : CutCodeSlot a) := placementRow E (W p.1) p.2.val
  let V (i : OmegaOneIndex) := tableAgreement u (decodeCutCode a (e i))
  have hV : (⨆ i,V i) = ⊤ := decodeCutCode_cover_r469 e hE a u
  have hFull : (⨆ i,baseEmbed Q (placementCut E W a ⊓ V i)) =
      baseEmbed Q (placementCut E W a) := by
    rw [← baseEmbed_joins_r427,← inf_iSup_eq,hV,inf_top_eq]
  apply le_iSup_of_le a
  rw [← hFull]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  let m := placementCut E W a ⊓ V i
  have h₁ := placement_truncated_value Q E f W a m inf_le_left n
  have h₂ := placementTableReal_mask Q E f a u (decodeCutCode a (e i)) m inf_le_right n
  exact h₁.trans h₂

end JSP000930.Negative
