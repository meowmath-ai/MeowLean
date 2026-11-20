import JSP000933PreparedSmallDiamondClosure

open Cardinal

namespace JSP000933
namespace PreparedModel

theorem smallDiamond_simultaneous_r402 {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I<GroundContinuumSucc) (Q : I→SmallDiamondCondition→Prop)
    (hDown : ∀ i {q r}, r≤q → Q i q → Q i r)
    (p : SmallDiamondCondition) (hDense : ∀ i q, q≤p → ∃ r≤q,Q i r) :
    ∃ q≤p,∀ i,Q i q := by
  classical
  let start (i : I) (prev : ∀ j : I,j< i→SmallDiamondCondition) : SmallDiamondCondition :=
    if h : ∃ q≤p,∀ j (hj : j< i),q≤prev j hj then Classical.choose h else p
  let next (i : I) (prev : ∀ j : I,j< i→SmallDiamondCondition) : SmallDiamondCondition :=
    if h : ∃ r≤start i prev,Q i r then Classical.choose h else start i prev
  let seq : I→SmallDiamondCondition := WellFounded.fix wellFounded_lt next
  have hSeq (i : I) : seq i=next i (fun j _ => seq j) :=
    WellFounded.fix_eq wellFounded_lt next i
  have hGood (i : I) : seq i≤p ∧ (∀ j< i,seq i≤seq j) ∧ Q i (seq i) := by
    refine wellFounded_lt.induction (C := fun i => seq i ≤ p ∧ (∀ j < i, seq i ≤ seq j) ∧ Q i (seq i)) i ?_
    intro i ih
    let prev (j : ↥(Set.Iio i)) := seq j.val
    have hPrevSmall : Cardinal.mk (↥(Set.Iio i))<GroundContinuumSucc :=
      (Cardinal.mk_subtype_le (fun j : I => j< i)).trans_lt hI
    have hPrevChain (j k : ↥(Set.Iio i)) : prev j≤prev k ∨ prev k≤prev j := by
      rcases lt_trichotomy j.val k.val with h | h | h
      · exact Or.inr ((ih k.val k.property).2.1 j.val h)
      · exact Or.inl (le_of_eq (congrArg seq h))
      · exact Or.inl ((ih j.val j.property).2.1 k.val h)
    have hHas : ∃ q≤p,∀ j (hj : j< i),q≤seq j := by
      by_cases hE : Nonempty (↥(Set.Iio i))
      · obtain ⟨q,hq⟩ := smallDiamond_chain_lower_r400 prev hPrevSmall hPrevChain
        obtain ⟨j⟩ := hE
        exact ⟨q,(hq j).trans (ih j.val j.property).1,fun k hk => hq ⟨k,hk⟩⟩
      · exact ⟨p,le_rfl,fun j hj => False.elim (hE ⟨⟨j,hj⟩⟩)⟩
    have hStart : start i (fun j _ => seq j)≤p ∧
        ∀ j< i,start i (fun j _ => seq j)≤seq j := by
      simpa only [start,dite_eq_left hHas] using Classical.choose_spec hHas
    have hN := hDense i (start i (fun j _ => seq j)) hStart.1
    have hNext : next i (fun j _ => seq j)≤start i (fun j _ => seq j) ∧
        Q i (next i (fun j _ => seq j)) := by
      simpa only [next,dite_eq_left hN] using Classical.choose_spec hN
    rw [hSeq i]
    exact ⟨hNext.1.trans hStart.1,fun j hj => hNext.1.trans (hStart.2 j hj),hNext.2⟩
  by_cases hE : Nonempty I
  · have hChain (i j : I) : seq i≤seq j ∨ seq j≤seq i := by
      rcases lt_trichotomy i j with h | h | h
      · exact Or.inr ((hGood j).2.1 i h)
      · exact Or.inl (le_of_eq (congrArg seq h))
      · exact Or.inl ((hGood i).2.1 j h)
    obtain ⟨q,hq⟩ := smallDiamond_chain_lower_r400 seq hI hChain
    obtain ⟨i⟩ := hE
    exact ⟨q,(hq i).trans (hGood i).1,fun j => hDown j (hq j) (hGood j).2.2⟩
  · exact ⟨p,le_rfl,fun i => False.elim (hE ⟨i⟩)⟩

theorem smallDiamond_simultaneous_wellOrder_r402 {I : Type}
    (hI : Cardinal.mk I<GroundContinuumSucc) (Q : I→SmallDiamondCondition→Prop)
    (hDown : ∀ i {q r}, r≤q → Q i q → Q i r)
    (p : SmallDiamondCondition) (hDense : ∀ i q, q≤p → ∃ r≤q,Q i r) :
    ∃ q≤p,∀ i,Q i q := by
  obtain ⟨L,hL⟩ := exists_wellFoundedLT I
  letI : LinearOrder I := L
  letI : WellFoundedLT I := hL
  exact smallDiamond_simultaneous_r402 hI Q hDown p hDense

end PreparedModel
end JSP000933
