import JSP000933RelativeNextDisjointLabel

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem iSup_chooseBool_r454 (a b : B) : (⨆ j : Bool,if j then b else a)=a⊔b := by
  apply le_antisymm
  · apply iSup_le
    intro j
    cases j
    · simpa using (le_sup_left : a≤a⊔b)
    · simpa using (le_sup_right : b≤a⊔b)
  · exact sup_le (le_iSup_of_le false (by simp)) (le_iSup_of_le true (by simp))

theorem unboundedValue_sup_r454 (hB : BoundsCountableOmegaOneNames B) (u v : OmegaOneIndex→B) :
    unboundedValue (fun i => u i⊔v i)=unboundedValue u⊔unboundedValue v := by
  let f (j : Bool) (i : OmegaOneIndex) := if j then v i else u i
  have hF : (fun i => ⨆ j,f j i)=(fun i => u i⊔v i) :=
    funext (fun i => iSup_chooseBool_r454 (u i) (v i))
  have hV : (fun j => unboundedValue (f j))=
      (fun j : Bool => if j then unboundedValue v else unboundedValue u) := by
    funext j
    cases j <;> rfl
  rw [← hF,unboundedValue_countableTypePartition_r443 hB,hV,iSup_chooseBool_r454]

theorem unboundedValue_of_disjoint_rows_r454 (u : OmegaOneIndex→B)
    (h : ∀ i j,i<j→Disjoint (u i) (u j)) : unboundedValue u=⊥ := by
  apply le_bot_iff.mp
  apply (unboundedValue_le_pairOverlap_r431 u).trans
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  exact disjoint_iff_inf_le.mp (h i j.val j.property)

open scoped Classical in
noncomputable def restrictLabels
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (P : LabelCandidate→Prop)
    (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : B :=
  if P (i,s) then W i s else ⊥

noncomputable def lastFiber (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (last : LabelCandidate→OmegaOneIndex) (c i : OmegaOneIndex) : B :=
  ⨆ s : {s : Finset OmegaOneIndex // last (i,s)=c},W i s.val

theorem lastFiber_bounded_r454 (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (last : LabelCandidate→OmegaOneIndex)
    (h : ∀ i j,i<j→∀ s t,last (i,s)=last (j,t) → Disjoint (W i s) (W j t))
    (c : OmegaOneIndex) : unboundedValue (lastFiber W last c)=⊥ := by
  apply unboundedValue_of_disjoint_rows_r454
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  simp only [lastFiber,iSup_inf_iSup]
  apply iSup_le
  rintro ⟨s,t⟩
  exact disjoint_iff_inf_le.mp (h i j hij s.val t.val (s.property.trans t.property.symm))

theorem initialClosedIndex_countable_r454 (e : OmegaOneIndex) : Countable (↥(Set.Iic e)) := by
  apply Set.countable_coe_iff.mpr
  apply ((OmegaOneIndex_initial_countable_r61 e).to_set.insert e).mono
  intro i hi
  rcases lt_or_eq_of_le (Set.mem_Iic.mp hi) with h | h
  · exact Set.mem_insert_of_mem _ h
  · exact Set.mem_insert_iff.mpr (Or.inl h)

theorem highLast_keepsUnbounded_r454 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (last : LabelCandidate→OmegaOneIndex)
    (h : ∀ i j,i<j→∀ s t,last (i,s)=last (j,t) → Disjoint (W i s) (W j t))
    (e : OmegaOneIndex) :
    unboundedValue (rowLabelWeight (restrictLabels W (fun x => e<last x)))=
      unboundedValue (rowLabelWeight W) := by
  classical
  let Low := restrictLabels W (fun x => last x≤e)
  let High := restrictLabels W (fun x => e<last x)
  letI : Countable (↥(Set.Iic e)) := initialClosedIndex_countable_r454 e
  have hLow : unboundedValue (rowLabelWeight Low)=⊥ := by
    apply le_bot_iff.mp
    have hLe (i : OmegaOneIndex) : rowLabelWeight Low i≤⨆ c : ↥(Set.Iic e),lastFiber W last c.val i := by
      apply iSup_le
      intro s
      by_cases hs : last (i,s)≤e
      · exact le_iSup_of_le (⟨last (i,s),hs⟩ : ↥(Set.Iic e))
          (le_iSup_of_le ⟨s,rfl⟩ (by simp only [Low,restrictLabels,ite_eq_left hs,le_rfl]))
      · simp only [Low,restrictLabels,ite_eq_right hs,bot_le]
    apply (unboundedValue_mono_r431 hLe).trans
    rw [unboundedValue_countableTypePartition_r443 hB]
    exact iSup_le (fun c => (lastFiber_bounded_r454 W last h c.val).le)
  have hJoin : rowLabelWeight W=(fun i => rowLabelWeight Low i⊔rowLabelWeight High i) := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro s
      by_cases hs : last (i,s)≤e
      · apply le_sup_of_le_left
        exact le_iSup_of_le s (by simp only [Low,restrictLabels,ite_eq_left hs,le_rfl])
      · apply le_sup_of_le_right
        exact le_iSup_of_le s (by simp only [High,restrictLabels,ite_eq_left (lt_of_not_ge hs),le_rfl])
    · apply sup_le
      · apply iSup_le
        intro s
        exact (show Low i s≤W i s by unfold Low restrictLabels; split <;> simp).trans (le_iSup _ s)
      · apply iSup_le
        intro s
        exact (show High i s≤W i s by unfold High restrictLabels; split <;> simp).trans (le_iSup _ s)
  rw [hJoin,unboundedValue_sup_r454 hB,hLow,bot_sup_eq]

end RelativeOCA
end JSP000933
