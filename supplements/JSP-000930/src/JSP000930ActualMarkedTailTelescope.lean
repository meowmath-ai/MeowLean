import JSP000930ActualAugmentedTailDensity

namespace JSP000930.Negative

open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA

noncomputable def actualTailArrow {d a : GroundContinuumSuccIndex}
    (hB : ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (i j : ClosedWetzelTail d a) (hij : i≤j) :
    LocalTraceInclusion (actualAugmentedQ i.val s) (actualAugmentedQ j.val s) u :=
  actualAugmentedLocalArrow hij (fun k hk => hB k (hk.trans_le j.property.2)) s u

theorem actualTailArrow_predense {d a : GroundContinuumSuccIndex}
    (hB : ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (hSep : ∀ j,d≤j → j<a → ∀ r t : s,r≠t →
      u ≤ (labelAgreement (preparedWetzelRows r.val j) (preparedWetzelRows t.val j))ᶜ) :
    ∀ (j i : ClosedWetzelTail d a) (hij : i≤j),
      PreservesPredensity (actualTailArrow hB s u i j hij).insideMap := by
  classical
  let I := ClosedWetzelTail d a
  let F (i j : I) (hij : i≤j) := actualTailArrow hB s u i j hij
  apply telescope_local_predensity930 F
  · intro i t
    exact actualAugmentedIncludeLabel_id i.val s t
  · intro i j k hij hjk t
    exact actualAugmentedIncludeLabel_comp hij hjk s t
  · intro b h₀
    by_cases hMax : ∃ i : I,i<b ∧ ∀ j : I,j < b → j ≤ i
    · exact Or.inl hMax
    · right
      intro p
      obtain ⟨i,hi⟩ := h₀
      have hd : d<b.val := i.property.1.trans_lt hi
      have hGap (j : GroundContinuumSuccIndex) (hj : d≤j) (hjb : j<b.val) : ∃ k,j<k ∧ k<b.val := by
        let t : I := ⟨j,hj,hjb.le.trans b.property.2⟩
        by_contra hn
        apply hMax
        exact ⟨t,hjb,fun z hz => le_of_not_gt (fun htz => hn ⟨z.val,htz,hz⟩)⟩
      have hL := checkedLimit_of_tailGap hd hGap
      obtain ⟨k,hk,hdk,q,hq⟩ := actualAugmented_earlierOnTail hd hL
        (fun j hj => hB j (hj.trans_le b.property.2)) s u p
      exact ⟨⟨k,hdk,hk.le.trans b.property.2⟩,hk,q,hq.le⟩
  · intro i j hij hMax
    have he := closedWetzelTail_immediate hij hMax
    have hia : i.val < a := (show i.val < j.val from hij).trans_le j.property.2
    have hOld (t : GroundContinuumSuccIndex) (ht : t ≤ i.val) : BoundsSmallKappaNames (ActualWorkBA t) :=
      hB t (ht.trans_lt hia)
    have hK := actualAugmented_nextPredense_onMark i.val s u (hSep i.val i.property.1 hia) hOld
    rcases j with ⟨j,hj⟩
    change wetzelGroundNext i.val = j at he
    subst j
    exact hK

end JSP000930.Negative
