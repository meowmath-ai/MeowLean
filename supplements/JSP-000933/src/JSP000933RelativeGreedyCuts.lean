import JSP000933RelativeGreedyMaximality

namespace JSP000933
namespace RelativeOCA

open MarkedForcing BooleanCompletion OpenGraphForcing CantorCodes

variable {B N I : Type} [CompleteBooleanAlgebra B]
variable [Preorder I] [WellFoundedLT I]

noncomputable def greedyRowActive (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) : B :=
  ⨆ n,greedyTraceWeight Q E x i n

theorem greedyRowActive_spec_r467 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) (n : N) :
    greedyTraceWeight Q E x i n=greedyRowActive Q E x i⊓E.cell i n := by
  apply le_antisymm
  · exact le_inf (le_iSup _ n) (greedyTraceWeight_cell_r465 Q E x i n)
  · unfold greedyRowActive
    rw [iSup_inf_eq]
    apply iSup_le
    intro k
    classical
    by_cases h : k=n
    · subst k
      exact inf_le_left
    · have hD : Disjoint (greedyTraceWeight Q E x i k) (E.cell i n) :=
        (E.rowApart i h).mono_left (greedyTraceWeight_cell_r465 Q E x i k)
      exact (disjoint_iff_inf_le.mp hD).trans bot_le

theorem traceRectangle_meet_base_r467 (Q : ValuedPoset B N) (n : N) (a b : B) :
    baseEmbed Q a⊓traceRectangle Q n b=traceRectangle Q n (a⊓b) := by
  unfold traceRectangle
  rw [baseEmbed_meets_r429,inf_assoc]

theorem traceRectangle_disjoint_base_r467 (Q : ValuedPoset B N) (n : N) {a b : B}
    (h : Disjoint a b) : baseEmbed Q a⊓traceRectangle Q n b=⊥ := by
  rw [traceRectangle_meet_base_r467,h.eq_bot,traceRectangle_zero_r464]

noncomputable def initialGreedyValue (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (x : TotalBA Q) (c : OmegaOneIndex) : TotalBA Q :=
  ⨆ i : ↥(Set.Iio c),⨆ n,traceRectangle Q n (greedyTraceWeight Q E x i.val n)

theorem initialGreedyValue_le_r467 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (x : TotalBA Q) (c : OmegaOneIndex) :
    initialGreedyValue Q E x c≤x := by
  apply iSup_le
  intro i
  apply iSup_le
  intro n
  exact (traceRectangle_accept_iff_r464 Q x n _).mpr
    (greedyTraceWeight_accepted_r465 Q E x i.val n)

theorem greedy_initial_on_cut_r467 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (x : TotalBA Q) (c : OmegaOneIndex)
    (m : B) (hm : ∀ i,c≤ i → Disjoint m (greedyRowActive Q E x i)) :
    baseEmbed Q m⊓x=baseEmbed Q m⊓initialGreedyValue Q E x c := by
  classical
  apply le_antisymm
  · calc
      baseEmbed Q m⊓x=baseEmbed Q m⊓greedyTraceValue Q E x :=
        congrArg (fun z => baseEmbed Q m⊓z) (greedyTraceValue_eq_r466 Q E x).symm
      _ ≤ _ := by
        unfold greedyTraceValue
        rw [inf_iSup_eq]
        apply iSup_le
        intro i
        rw [inf_iSup_eq]
        apply iSup_le
        intro n
        by_cases hi : i<c
        · exact le_inf inf_le_left (inf_le_right.trans (le_iSup_of_le (⟨i,hi⟩ : ↥(Set.Iio c))
            (le_iSup (fun k => traceRectangle Q k (greedyTraceWeight Q E x i k)) n)))
        · have h := (hm i (le_of_not_gt hi)).mono_right
            (show greedyTraceWeight Q E x i n≤greedyRowActive Q E x i from le_iSup _ n)
          rw [traceRectangle_disjoint_base_r467 Q n h]
          exact bot_le
  · exact inf_le_inf le_rfl (initialGreedyValue_le_r467 Q E x c)

end RelativeOCA
end JSP000933
