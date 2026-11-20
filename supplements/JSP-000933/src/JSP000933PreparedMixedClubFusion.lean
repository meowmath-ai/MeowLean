import JSP000933PreparedMixedClubStep

open Cardinal

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem exists_preparedFusionStages_r409 {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I<GroundContinuumSucc) (A C : GroundContinuumSuccIndex→PreparedBA)
    (mark : PreparedBA) (hU : ∀ a,mark≤aboveClub C a)
    (p : CollapseBasicCondition) (q : SmallDiamondCondition)
    (hM : imageCondition ((p,q) : PreparedCondition) ≤ mark) :
    ∃ f g : I→SmallDiamondCondition,
      (∀ i,f i≤q) ∧ (∀ i j,j< i→f i≤g j) ∧
      ∀ i,PreparedFusionStep A C p (f i) (g i) := by
  classical
  let Stage := SmallDiamondCondition×SmallDiamondCondition
  let start (i : I) (prev : ∀ j : I,j< i→Stage) : SmallDiamondCondition :=
    if h : ∃ s≤q,∀ j (hj : j< i),s≤(prev j hj).2 then Classical.choose h else q
  let take (i : I) (prev : ∀ j : I,j< i→Stage) : Stage :=
    let s := start i prev
    (s,if h : imageCondition ((p,s) : PreparedCondition) ≤ mark then
      Classical.choose (exists_preparedFusionStep_r408 A C mark hU p s h) else s)
  let seq : I→Stage := WellFounded.fix wellFounded_lt take
  have hSeq (i : I) : seq i=take i (fun j _ => seq j) :=
    WellFounded.fix_eq wellFounded_lt take i
  have hGood (i : I) : (seq i).1≤q ∧ (∀ j< i,(seq i).1≤(seq j).2) ∧
      PreparedFusionStep A C p (seq i).1 (seq i).2 := by
    refine wellFounded_lt.induction (C := fun i => (seq i).1 ≤ q ∧
      (∀ j < i, (seq i).1 ≤ (seq j).2) ∧ PreparedFusionStep A C p (seq i).1 (seq i).2) i ?_
    intro i ih
    let out (j : ↥(Set.Iio i)) := (seq j.val).2
    have hSmall : Cardinal.mk (↥(Set.Iio i))<GroundContinuumSucc :=
      (Cardinal.mk_subtype_le (fun j : I => j< i)).trans_lt hI
    have hChain (j k : ↥(Set.Iio i)) : out j≤out k ∨ out k≤out j := by
      rcases lt_trichotomy j.val k.val with h | h | h
      · exact Or.inr ((ih k.val k.property).2.2.stronger.trans ((ih k.val k.property).2.1 j.val h))
      · exact Or.inl (le_of_eq (congrArg (fun j => (seq j).2) h))
      · exact Or.inl ((ih j.val j.property).2.2.stronger.trans ((ih j.val j.property).2.1 k.val h))
    have hHas : ∃ s≤q,∀ j (hj : j< i),s≤(seq j).2 := by
      by_cases hE : Nonempty (↥(Set.Iio i))
      · obtain ⟨s,hs⟩ := smallDiamond_chain_lower_r400 out hSmall hChain
        obtain ⟨j⟩ := hE
        exact ⟨s,(hs j).trans ((ih j.val j.property).2.2.stronger.trans (ih j.val j.property).1),
          fun k hk => hs ⟨k,hk⟩⟩
      · exact ⟨q,le_rfl,fun j hj => False.elim (hE ⟨⟨j,hj⟩⟩)⟩
    have hStart : start i (fun j _ => seq j)≤q ∧
        ∀ j< i,start i (fun j _ => seq j)≤(seq j).2 := by
      simpa only [start,dite_eq_left hHas] using Classical.choose_spec hHas
    let s := start i (fun j _ => seq j)
    have hMark : imageCondition ((p,s) : PreparedCondition) ≤ mark :=
      (imageCondition_mono_r50 (show ((p,s) : PreparedCondition)≤(p,q) from
        ⟨le_rfl,hStart.1⟩)).trans hM
    have hStep := Classical.choose_spec (exists_preparedFusionStep_r408 A C mark hU p s hMark)
    have he : seq i=(s,Classical.choose
        (exists_preparedFusionStep_r408 A C mark hU p s hMark)) := by
      rw [hSeq i]
      change (s,(if h : imageCondition ((p,s) : PreparedCondition) ≤ mark then _ else s))=_
      rw [dite_eq_left hMark]
    rw [he]
    exact ⟨hStart.1,hStart.2,hStep⟩
  exact ⟨fun i => (seq i).1,fun i => (seq i).2,fun i => (hGood i).1,
    fun i j hj => (hGood i).2.1 j hj,fun i => (hGood i).2.2⟩

end PreparedModel
end JSP000933
