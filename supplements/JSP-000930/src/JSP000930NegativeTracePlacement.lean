import JSP000933RelativeSmallQuotientCH
import JSP000933GroundKappaTraceEnum

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes

variable {B I N : Type} [CompleteBooleanAlgebra B]

noncomputable def firstTracePlacement (E : MixedEnumeration OmegaOneIndex I B)
    (r : OmegaOneIndex) (j : I) : B :=
  firstChoiceCell (fun a => E.cell a j) r

theorem firstTracePlacement_le (E : MixedEnumeration OmegaOneIndex I B)
    (r : OmegaOneIndex) (j : I) : firstTracePlacement E r j ≤ E.cell r j :=
  firstChoiceCell_le_r435 _ _

theorem firstTracePlacement_full (E : MixedEnumeration OmegaOneIndex I B) (j : I) :
    (⨆ r,firstTracePlacement E r j) = ⊤ :=
  (firstChoiceCell_join_r435 _).trans (E.colFull j)

theorem firstTracePlacement_rowsApart (E : MixedEnumeration OmegaOneIndex I B)
    (r : OmegaOneIndex) {j k : I} (h : j ≠ k) :
    Disjoint (firstTracePlacement E r j) (firstTracePlacement E r k) :=
  ((E.rowApart r h).mono_left (firstTracePlacement_le E r j)).mono_right (firstTracePlacement_le E r k)

theorem firstTracePlacement_colsApart (E : MixedEnumeration OmegaOneIndex I B)
    {r s : OmegaOneIndex} (h : r < s) (j : I) :
    Disjoint (firstTracePlacement E r j) (firstTracePlacement E s j) :=
  firstChoiceCell_disjoint_r435 _ _ _ h

noncomputable def placementWeight (E : MixedEnumeration OmegaOneIndex I B)
    (W : I → B) (r : OmegaOneIndex) (j : I) : B := W j ⊓ firstTracePlacement E r j

noncomputable def placementRow (E : MixedEnumeration OmegaOneIndex I B)
    (W : I → B) (r : OmegaOneIndex) : B := ⨆ j,placementWeight E W r j

theorem placementWeight_split (E : MixedEnumeration OmegaOneIndex I B)
    (W : I → B) (r : OmegaOneIndex) (j : I) :
    placementWeight E W r j = placementRow E W r ⊓ firstTracePlacement E r j := by
  classical
  apply le_antisymm
  · exact le_inf (le_iSup _ j) inf_le_right
  · unfold placementRow
    rw [iSup_inf_eq]
    apply iSup_le
    intro k
    by_cases h : k = j
    · subst k
      exact inf_le_left
    · have hD := (firstTracePlacement_rowsApart E r h).mono_left
        (show placementWeight E W r k ≤ firstTracePlacement E r k from inf_le_right)
      exact (disjoint_iff_inf_le.mp (show
        Disjoint (placementWeight E W r k) (firstTracePlacement E r j) from hD)).trans bot_le

theorem placementWeight_column_cover (E : MixedEnumeration OmegaOneIndex I B)
    (W : I → B) (j : I) :
    (⨆ r,placementWeight E W r j) = W j := by
  unfold placementWeight
  rw [← inf_iSup_eq,firstTracePlacement_full,inf_top_eq]

end JSP000930.Negative
