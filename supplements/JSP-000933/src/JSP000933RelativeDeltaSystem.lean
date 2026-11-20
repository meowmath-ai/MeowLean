import JSP000933RelativeJoinedSupportWeights
import JSP000933RelativeCountablePigeonhole

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

structure DeltaSupportThinning (W : OmegaOneIndex → Finset I → B) (m : B) where
  root : Finset I
  mark : B
  mark_le : mark ≤ m
  mark_positive : mark ≠ ⊥
  weight : OmegaOneIndex → Finset I → B
  weight_le : ∀ i s, weight i s ≤ W i s
  staysUnbounded : mark ≤ unboundedValue (rowSupportWeight weight)
  disjoint_bad : ∀ i j, i<j → ∀ s t, s∩t≠root →
    Disjoint (weight i s) (weight j t)

theorem exists_delta_of_all_fibers_bounded
    (hB : BoundsCountableOmegaOneNames B) (W : OmegaOneIndex → Finset I → B)
    (m : B) (hm : m ≠ ⊥) (hW : m ≤ unboundedValue (rowSupportWeight W))
    (hFibers : ∀ v, m ≤ (unboundedValue (supportFiber W v))ᶜ) :
    Nonempty (DeltaSupportThinning W m) := by
  obtain ⟨S⟩ := exists_relativeDisjointSupports_c15 hB W m hW hFibers
  refine ⟨⟨∅,m,le_rfl,hm,joinedSupportWeight S,joinedSupportWeight_le_c16 S,
    joinedSupportWeight_unbounded_c16 S,?_⟩⟩
  intro i j hij s t hbad
  have hp : (i,s) ≠ (j,t) := fun h => hij.ne (congrArg Prod.fst h)
  have hDisj : ¬ Disjoint s t := by
    intro h
    apply hbad
    ext v
    simp only [Finset.mem_inter,Finset.notMem_empty,iff_false]
    exact fun hv => (Finset.disjoint_left.mp h) hv.1 hv.2
  exact joinedSupportWeight_disjoint_invalidPair_c16 S (i,s) (j,t) hp (Or.inr hDisj)

noncomputable def eraseSupportWeights (W : OmegaOneIndex → Finset I → B) (v : I)
    (i : OmegaOneIndex) (t : Finset I) : B :=
  ⨆ s : {s : Finset I // v∈s ∧ s.erase v=t}, W i s.val

theorem row_eraseSupportWeights (W : OmegaOneIndex → Finset I → B) (v : I) :
    rowSupportWeight (eraseSupportWeights W v) = supportFiber W v := by
  funext i
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro s
    exact le_iSup (fun z : {z : Finset I // v ∈ z} => W i z.val) ⟨s.val,s.property.1⟩
  · apply iSup_le
    intro s
    exact le_iSup_of_le (s.val.erase v) (le_iSup (fun z : {z : Finset I // v ∈ z ∧ z.erase v = s.val.erase v} => W i z.val)
      ⟨s.val,s.property,rfl⟩)

noncomputable def restoreSupportWeights (W U : OmegaOneIndex → Finset I → B) (v : I)
    (i : OmegaOneIndex) (s : Finset I) : B :=
  if v∈s then W i s ⊓ U i (s.erase v) else ⊥

theorem row_restoreSupportWeights (W U : OmegaOneIndex → Finset I → B) (v : I)
    (hU : ∀ i t, U i t ≤ eraseSupportWeights W v i t) :
    rowSupportWeight (restoreSupportWeights W U v) = rowSupportWeight U := by
  funext i
  apply le_antisymm
  · apply iSup_le
    intro s
    by_cases hs : v∈s
    · rw [restoreSupportWeights,ite_eq_left hs]
      exact inf_le_right.trans (le_iSup _ (s.erase v))
    · rw [restoreSupportWeights,ite_eq_right hs]
      exact bot_le
  · apply iSup_le
    intro t
    have ht := hU i t
    rw [eraseSupportWeights] at ht
    calc
      U i t = U i t ⊓ (⨆ s : {s : Finset I // v∈s ∧ s.erase v=t},W i s.val) :=
        (inf_eq_left.mpr ht).symm
      _ = ⨆ s : {s : Finset I // v∈s ∧ s.erase v=t}, U i t ⊓ W i s.val := inf_iSup_eq _ _
      _ ≤ _ := by
        apply iSup_le
        intro s
        apply le_iSup_of_le s.val
        rw [restoreSupportWeights,ite_eq_left s.property.1,s.property.2,inf_comm]

theorem restoreSupport_pair_inter {s t r : Finset I} {v : I}
    (hs : v∈s) (ht : v∈t) (h : s.erase v ∩ t.erase v = r) :
    s∩t=insert v r := by
  ext x
  by_cases hx : x=v
  · subst x
    simp [hs,ht]
  · have h' : x ∈ s.erase v ∩ t.erase v ↔ x ∈ r := by rw [h]
    simpa [Finset.mem_inter,Finset.mem_erase,Finset.mem_insert,hx] using h'

noncomputable def DeltaSupportThinning.liftErase {W : OmegaOneIndex → Finset I → B} {m m' : B}
    (hm' : m' ≤ m) (v : I) (D : DeltaSupportThinning (eraseSupportWeights W v) m') :
    DeltaSupportThinning W m where
  root := insert v D.root
  mark := D.mark
  mark_le := D.mark_le.trans hm'
  mark_positive := D.mark_positive
  weight := restoreSupportWeights W D.weight v
  weight_le := by
    intro i s
    unfold restoreSupportWeights
    split
    · exact inf_le_left
    · exact bot_le
  staysUnbounded := by
    rw [row_restoreSupportWeights W D.weight v D.weight_le]
    exact D.staysUnbounded
  disjoint_bad := by
    intro i j hij s t hbad
    by_cases hs : v∈s
    · by_cases ht : v∈t
      · simp only [restoreSupportWeights,ite_eq_left hs,ite_eq_left ht]
        have hErase : s.erase v ∩ t.erase v ≠ D.root :=
          fun he => hbad (restoreSupport_pair_inter hs ht he)
        exact ((D.disjoint_bad i j hij _ _ hErase).mono_left inf_le_right).mono_right inf_le_right
      · simp only [restoreSupportWeights,ite_eq_right ht,disjoint_bot_right]
    · simp only [restoreSupportWeights,ite_eq_right hs,disjoint_bot_left]

theorem exists_relative_delta_uniform
    (hB : BoundsCountableOmegaOneNames B) (n : ℕ)
    (W : OmegaOneIndex → Finset I → B) (m : B) (hm : m ≠ ⊥)
    (hW : m ≤ unboundedValue (rowSupportWeight W))
    (hCard : ∀ i s, s.card ≠ n → W i s = ⊥) :
    Nonempty (DeltaSupportThinning W m) := by
  classical
  induction n generalizing W m with
  | zero =>
    apply exists_delta_of_all_fibers_bounded hB W m hm hW
    intro v
    have hz : supportFiber W v = fun _ => (⊥ : B) := by
      funext i
      apply le_bot_iff.mp
      apply iSup_le
      intro s
      exact (hCard i s.val (Finset.card_pos.mpr ⟨v,s.property⟩).ne').le
    rw [hz,unboundedValue_zero_r443,compl_bot]
    exact le_top
  | succ n ih =>
    by_cases h : ∃ v, m ⊓ unboundedValue (supportFiber W v) ≠ ⊥
    · obtain ⟨v,hv⟩ := h
      let m' := m ⊓ unboundedValue (supportFiber W v)
      have he : m' ≤ unboundedValue (rowSupportWeight (eraseSupportWeights W v)) := by
        rw [row_eraseSupportWeights]
        exact inf_le_right
      have hc (i : OmegaOneIndex) (t : Finset I) (ht : t.card ≠ n) :
          eraseSupportWeights W v i t = ⊥ := by
        apply le_bot_iff.mp
        apply iSup_le
        intro s
        have hs : s.val.card ≠ n+1 := by
          intro hz
          have he := Finset.card_erase_of_mem s.property.1
          rw [s.property.2,hz] at he
          exact ht (by omega)
        exact (hCard i s.val hs).le
      obtain ⟨D⟩ := ih (eraseSupportWeights W v) m' hv he hc
      exact ⟨D.liftErase inf_le_left v⟩
    · apply exists_delta_of_all_fibers_bounded hB W m hm hW
      intro v
      apply le_compl_iff_disjoint_right.mpr
      have hh : m ⊓ unboundedValue (supportFiber W v) = ⊥ := by
        by_contra hn
        exact h ⟨v,hn⟩
      exact disjoint_iff_inf_le.mpr hh.le

theorem exists_relative_delta
    (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex → Finset I → B) (m : B) (hm : m ≠ ⊥)
    (hW : m ≤ unboundedValue (rowSupportWeight W)) :
    Nonempty (DeltaSupportThinning W m) := by
  classical
  let V (n : ℕ) (i : OmegaOneIndex) (s : Finset I) := if s.card=n then W i s else ⊥
  have hV (n i s) : V n i s ≤ W i s := by
    unfold V
    split
    · exact le_rfl
    · exact bot_le
  have hrow : rowSupportWeight W = fun i => ⨆ n, rowSupportWeight (V n) i := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro s
      exact le_iSup_of_le s.card (le_iSup_of_le s (by simp [V]))
    · exact iSup_le (fun n => iSup_le (fun s => le_iSup_of_le s (hV n i s)))
  have hSplit : m ≤ ⨆ n,unboundedValue (rowSupportWeight (V n)) := by
    rwa [hrow,unboundedValue_countablePartition_r433 hB] at hW
  have hPos : ∃ n, m ⊓ unboundedValue (rowSupportWeight (V n)) ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hm
    calc
      m = m ⊓ (⨆ n,unboundedValue (rowSupportWeight (V n))) := (inf_eq_left.mpr hSplit).symm
      _ = ⨆ n, m ⊓ unboundedValue (rowSupportWeight (V n)) := inf_iSup_eq _ _
      _ = ⊥ := le_bot_iff.mp (iSup_le (fun n => (h n).le))
  obtain ⟨n,hn⟩ := hPos
  obtain ⟨D⟩ := exists_relative_delta_uniform hB n (V n) _ hn inf_le_right
    (fun i s hs => ite_eq_right hs)
  exact ⟨⟨D.root,D.mark,D.mark_le.trans inf_le_left,D.mark_positive,D.weight,
    fun i s => (D.weight_le i s).trans (hV n i s),D.staysUnbounded,D.disjoint_bad⟩⟩

end RelativeOCA
end JSP000933
