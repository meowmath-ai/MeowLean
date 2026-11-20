import JSP000933RelativeDisjointLabelSequence

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]
variable {W : OmegaOneIndex→Finset OmegaOneIndex→B} {m : B}

theorem relativePickRowBound_r449 (S : RelativeDisjointLabels W m) (i : OmegaOneIndex)
    (x : LabelCandidate) (hx : x.1< i) : (S.pick i).value x=⊥ := by
  classical
  suffices h : ∀ i : OmegaOneIndex,∀ x : LabelCandidate,x.1< i→(S.pick i).value x=⊥ from h i x hx
  intro j
  refine wellFounded_lt.induction (C := fun j => ∀ x : LabelCandidate, x.1 < j → (S.pick j).value x = ⊥) j ?_
  intro j ih x hxj
  let r := (S.pick j).value x
  have hOld : r≤⨆ y,(S.pick x.1).value y :=
    ((S.pick j).each_le x).trans_eq (S.pick x.1).covers.symm
  apply le_bot_iff.mp
  apply (le_inf hOld le_rfl).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro y
  by_cases hy : y.1<x.1
  · rw [ih x.1 hxj y hy,bot_inf_eq]
  · have hN : ¬laterDisjoint y x := fun h => hy h.1
    change (S.pick x.1).value y⊓(S.pick j).value x≤⊥
    simpa only [laterDisjointValue,ite_eq_right hN] using relativeDisjointLabels_overlap_r448 S hxj y x

noncomputable def joinedLabelWeight (S : RelativeDisjointLabels W m)
    (i : OmegaOneIndex) (a : Finset OmegaOneIndex) : B :=
  ⨆ j,(S.pick j).value (i,a)

theorem joinedLabelWeight_le_r449 (S : RelativeDisjointLabels W m)
    (i : OmegaOneIndex) (a : Finset OmegaOneIndex) :
    joinedLabelWeight S i a≤W i a :=
  iSup_le (fun j => S.admissible j (i,a))

theorem joinedLabelWeight_unbounded_r449 (S : RelativeDisjointLabels W m) :
    m≤unboundedValue (rowLabelWeight (joinedLabelWeight S)) := by
  apply le_iInf
  intro b
  obtain ⟨j,hj⟩ := OmegaOneIndex_countable_bounded_r61 {b} (Set.countable_singleton b)
  have hBJ : b<j := hj b (Set.mem_singleton _)
  apply (S.pick j).covers.ge.trans
  apply iSup_le
  intro x
  by_cases hx : b<x.1
  · exact le_iSup_of_le (⟨x.1,hx⟩ : {i : OmegaOneIndex // b < i})
      (le_iSup_of_le x.2 (le_iSup (fun k => (S.pick k).value (x.1,x.2)) j))
  · rw [relativePickRowBound_r449 S j x ((le_of_not_gt hx).trans_lt hBJ)]
    exact bot_le

theorem joinedLabelWeight_disjoint_invalidPair_r449 (S : RelativeDisjointLabels W m)
    (x y : LabelCandidate) (hne : x≠y)
    (hBad : x.1=y.1 ∨ ¬Disjoint x.2 y.2) :
    Disjoint (joinedLabelWeight S x.1 x.2) (joinedLabelWeight S y.1 y.2) := by
  classical
  have hXY : ¬laterDisjoint x y := fun h => hBad.elim
    (fun he => (lt_irrefl _ (he ▸ h.1))) (fun hd => hd h.2)
  have hYX : ¬laterDisjoint y x := fun h => hBad.elim
    (fun he => (lt_irrefl _ (he.symm ▸ h.1))) (fun hd => hd h.2.symm)
  apply disjoint_iff_inf_le.mpr
  simp only [joinedLabelWeight,iSup_inf_iSup]
  apply iSup_le
  rintro ⟨i,j⟩
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := relativeDisjointLabels_overlap_r448 S h x y
    simpa only [laterDisjointValue,ite_eq_right hXY] using h1
  · exact disjoint_iff_inf_le.mp ((S.pick i).disjoint hne)
  · rw [inf_comm]
    have h1 := relativeDisjointLabels_overlap_r448 S h y x
    simpa only [laterDisjointValue,ite_eq_right hYX] using h1

end RelativeOCA
end JSP000933
