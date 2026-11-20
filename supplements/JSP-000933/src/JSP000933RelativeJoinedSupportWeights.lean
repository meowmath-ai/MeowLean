import JSP000933RelativeDisjointSupportSequence

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]
variable {W : OmegaOneIndex→Finset I→B} {m : B}

theorem relativeSupportPickRowBound_c16 (S : RelativeDisjointSupports W m) (i : OmegaOneIndex)
    (x : (SupportCandidate I)) (hx : x.1< i) : (S.pick i).value x=⊥ := by
  classical
  suffices h : ∀ i : OmegaOneIndex,∀ x : (SupportCandidate I),x.1< i→(S.pick i).value x=⊥ from h i x hx
  intro j
  refine wellFounded_lt.induction (C := fun j => ∀ x : SupportCandidate I, x.1 < j → (S.pick j).value x = ⊥) j ?_
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
  · have hN : ¬laterSupportDisjoint y x := fun h => hy h.1
    change (S.pick x.1).value y⊓(S.pick j).value x≤⊥
    simpa only [laterSupportDisjointValue,ite_eq_right hN] using relativeDisjointSupports_overlap_c15 S hxj y x

noncomputable def joinedSupportWeight (S : RelativeDisjointSupports W m)
    (i : OmegaOneIndex) (a : Finset I) : B :=
  ⨆ j,(S.pick j).value (i,a)

theorem joinedSupportWeight_le_c16 (S : RelativeDisjointSupports W m)
    (i : OmegaOneIndex) (a : Finset I) :
    joinedSupportWeight S i a≤W i a :=
  iSup_le (fun j => S.admissible j (i,a))

theorem joinedSupportWeight_unbounded_c16 (S : RelativeDisjointSupports W m) :
    m≤unboundedValue (rowSupportWeight (joinedSupportWeight S)) := by
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
  · rw [relativeSupportPickRowBound_c16 S j x ((le_of_not_gt hx).trans_lt hBJ)]
    exact bot_le

theorem joinedSupportWeight_disjoint_invalidPair_c16 (S : RelativeDisjointSupports W m)
    (x y : (SupportCandidate I)) (hne : x≠y)
    (hBad : x.1=y.1 ∨ ¬Disjoint x.2 y.2) :
    Disjoint (joinedSupportWeight S x.1 x.2) (joinedSupportWeight S y.1 y.2) := by
  classical
  have hXY : ¬laterSupportDisjoint x y := fun h => hBad.elim
    (fun he => (lt_irrefl _ (he ▸ h.1))) (fun hd => hd h.2)
  have hYX : ¬laterSupportDisjoint y x := fun h => hBad.elim
    (fun he => (lt_irrefl _ (he.symm ▸ h.1))) (fun hd => hd h.2.symm)
  apply disjoint_iff_inf_le.mpr
  simp only [joinedSupportWeight,iSup_inf_iSup]
  apply iSup_le
  rintro ⟨i,j⟩
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := relativeDisjointSupports_overlap_c15 S h x y
    simpa only [laterSupportDisjointValue,ite_eq_right hXY] using h1
  · exact disjoint_iff_inf_le.mp ((S.pick i).disjoint hne)
  · rw [inf_comm]
    have h1 := relativeDisjointSupports_overlap_c15 S h y x
    simpa only [laterSupportDisjointValue,ite_eq_right hYX] using h1

end RelativeOCA
end JSP000933
