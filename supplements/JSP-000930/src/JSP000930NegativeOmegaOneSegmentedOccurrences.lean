import JSP000930NegativeRelativePressingDown
import JSP000933RelativeDiscreteChoices

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {B J : Type} [CompleteBooleanAlgebra B]

open scoped Classical in
noncomputable def occurrenceBefore (rank row : J → OmegaOneIndex) (x y : J) : B :=
  if rank x < row y then ⊤ else ⊥

open scoped Classical in
noncomputable def occurrenceBelow (rank : J → OmegaOneIndex) (x : J) (b : OmegaOneIndex) : B :=
  if rank x ≤ b then ⊤ else ⊥

theorem occurrenceBelow_mono (rank : J → OmegaOneIndex) (x : J) :
    Monotone (occurrenceBelow (B := B) rank x) := by
  intro a b hab
  by_cases h : rank x ≤ a
  · simp only [occurrenceBelow,ite_eq_left h,ite_eq_left (h.trans hab),le_rfl]
  · simp only [occurrenceBelow,ite_eq_right h,bot_le]

theorem occurrenceBelow_le_before (rank row : J → OmegaOneIndex) (x y : J)
    (b : OmegaOneIndex) (hb : b < row y) :
    (occurrenceBelow rank x b : B) ≤ occurrenceBefore rank row x y := by
  by_cases h : rank x ≤ b
  · simp only [occurrenceBelow,occurrenceBefore,ite_eq_left h,ite_eq_left (h.trans_lt hb),le_rfl]
  · simp only [occurrenceBelow,ite_eq_right h,bot_le]

theorem choose_next_omegaOccurrence {I : Type} [Countable I]
    (hB : BoundsCountableOmegaOneNames B) (rank row : J → OmegaOneIndex)
    (W : J → B) (m : B)
    (hTail : ∀ b,m ≤ ⨆ y : {y : J // b < row y},W y.val)
    (old : I → DiscreteChoiceOn J m) :
    ∃ C : DiscreteChoiceOn J m,(∀ y,C.value y ≤ W y) ∧
      ∀ i y,C.value y ≤ guardByChoice (old i) (fun x => occurrenceBefore rank row x y) := by
  let V (i : I) (b : OmegaOneIndex) :=
    guardByChoice (old i) (fun x => occurrenceBelow rank x b)
  have hV (i : I) : m ≤ ⨆ b,V i b := by
    apply guardByChoice_coversCutoffs_r445
    intro x
    apply le_iSup_of_le (rank x)
    simp only [occurrenceBelow,ite_eq_left le_rfl,le_top]
  let All (b : OmegaOneIndex) := ⨅ i,V i b
  have hAll : m ≤ ⨆ b,All b := uniform_countable_cutoffs_r444 hB m V
    (fun i _ _ h => guardByChoice_mono_r445 (old i) (fun x => occurrenceBelow_mono rank x h)) hV
  let U (y : J) := W y ⊓ ⨅ i,guardByChoice (old i) (fun x => occurrenceBefore rank row x y)
  have hU : m ≤ ⨆ y,U y := by
    apply (le_inf le_rfl hAll).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro b
    apply (le_inf le_rfl (inf_le_left.trans (hTail b))).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro y
    apply le_iSup_of_le y.val
    apply le_inf inf_le_right
    apply le_iInf
    intro i
    have h : (m ⊓ All b) ⊓ W y.val ≤ V i b :=
      inf_le_left.trans (inf_le_right.trans (iInf_le _ i))
    exact h.trans (guardByChoice_mono_r445 (old i)
      (fun x => occurrenceBelow_le_before rank row x y.val b y.property))
  obtain ⟨C,hC⟩ := exists_discreteChoiceOn_r445 m U hU
  exact ⟨C,fun y => (hC y).trans inf_le_left,
    fun i y => (hC y).trans (inf_le_right.trans (iInf_le _ i))⟩

structure SegmentedOmegaChoices (rank row : J → OmegaOneIndex) (W : J → B) (m : B) where
  pick : OmegaOneIndex → DiscreteChoiceOn J m
  valid : ∀ i x,(pick i).value x ≤ W x
  separated : ∀ i j,i < j → ∀ y,(pick j).value y ≤
    guardByChoice (pick i) (fun x => occurrenceBefore rank row x y)

theorem exists_segmentedOmegaChoices (hB : BoundsCountableOmegaOneNames B)
    (rank row : J → OmegaOneIndex) (W : J → B) (m : B)
    (hTail : ∀ b,m ≤ ⨆ y : {y : J // b < row y},W y.val) :
    Nonempty (SegmentedOmegaChoices rank row W m) := by
  classical
  let Good := {C : DiscreteChoiceOn J m // ∀ x,C.value x ≤ W x}
  have hStep (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i < j → Good) :
      ∃ C : DiscreteChoiceOn J m,(∀ x,C.value x ≤ W x) ∧
        ∀ (i : {i : OmegaOneIndex // i < j}) y,
          C.value y ≤ guardByChoice (prev i.val i.property).val
            (fun x => occurrenceBefore rank row x y) := by
    letI : Countable {i : OmegaOneIndex // i < j} := OmegaOneIndex_initial_countable_r61 j
    exact choose_next_omegaOccurrence hB rank row W m hTail (fun i : {i : OmegaOneIndex // i < j} => (prev i.val i.property).val)
  let next (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i < j → Good) : Good :=
    ⟨Classical.choose (hStep j prev),(Classical.choose_spec (hStep j prev)).1⟩
  let s : OmegaOneIndex → Good := WellFounded.fix wellFounded_lt next
  have hs (j : OmegaOneIndex) : s j = next j (fun i _ => s i) :=
    WellFounded.fix_eq wellFounded_lt next j
  refine ⟨⟨fun i => (s i).val,fun i => (s i).property,fun i j hij y => ?_⟩⟩
  change (s j).val.value y ≤ guardByChoice (s i).val (fun x => occurrenceBefore rank row x y)
  conv_lhs => rw [hs j]
  exact (Classical.choose_spec (hStep j (fun i _ => s i))).2 ⟨i,hij⟩ y

end JSP000930.Negative
