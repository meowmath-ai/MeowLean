import JSP000930ActualAugmentedMarkedSuccessor

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA

theorem actualAugmented_earlierOnTail {d a : GroundContinuumSuccIndex} (hd : d<a)
    (hL : CheckedGroundLimit a) (hB : ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (p : MaskedCondition (actualAugmentedQ a s) u) :
    ∃ (k : GroundContinuumSuccIndex) (hk : k<a) (_ : d≤k) (q : MaskedCondition (actualAugmentedQ k s) u),
      (actualAugmentedLocalArrow hk.le hB s u).insideMap q = p := by
  obtain ⟨j,hj,r,hr⟩ := actualAugmentedBasis_earlier hL s p.val.trace
  let k := max d j
  have hk : k<a := max_lt hd hj
  have hjk : j≤k := le_max_right _ _
  let label := actualAugmentedIncludeLabel hjk s r
  have he : actualAugmentedIncludeLabel hk.le s label = p.val.trace :=
    (actualAugmentedIncludeLabel_comp hjk hk.le s r).trans hr
  have hV : (actualAugmentedQ a s).valid p.val.trace = (actualAugmentedQ k s).valid label :=
    he ▸ actualAugmented_valid_transport hk.le s label
  let q : MaskedCondition (actualAugmentedQ k s) u :=
    ⟨⟨p.val.mask,label,p.val.nonzero,p.val.valid.trans_eq hV⟩,p.property⟩
  refine ⟨k,hk,le_max_left _ _,q,?_⟩
  apply Subtype.ext
  exact totalCondition_eq_of_data _ _ rfl he

abbrev ClosedWetzelTail (d a : GroundContinuumSuccIndex) :=
  {j : GroundContinuumSuccIndex // d≤j ∧ j≤a}

abbrev OpenWetzelTail (d a : GroundContinuumSuccIndex) :=
  {j : GroundContinuumSuccIndex // d≤j ∧ j<a}

theorem checkedLimit_of_tailGap {d a : GroundContinuumSuccIndex} (hd : d<a)
    (hGap : ∀ j,d≤j → j<a → ∃ k,j<k ∧ k<a) : CheckedGroundLimit a := by
  refine ⟨⟨d,hd⟩,?_⟩
  intro j hj
  by_cases h : d≤j
  · exact hGap j h hj
  · exact ⟨d,lt_of_not_ge h,hd⟩

theorem closedWetzelTail_immediate {d a : GroundContinuumSuccIndex} {i j : ClosedWetzelTail d a}
    (hij : i < j) (hMax : ∀ k : ClosedWetzelTail d a,k < j → k ≤ i) :
    wetzelGroundNext i.val = j.val := by
  have hnext : wetzelGroundNext i.val≤j.val := wetzelGroundNext_le_of_lt hij
  by_contra hn
  have hj : wetzelGroundNext i.val<j.val := hnext.lt_of_ne hn
  have hi : i.val<wetzelGroundNext i.val := (wetzelGroundNext_spec _ _).mpr le_rfl
  let k : ClosedWetzelTail d a := ⟨wetzelGroundNext i.val,i.property.1.trans hi.le,
    hnext.trans j.property.2⟩
  exact hi.not_ge (hMax k hj)

end JSP000930.Negative
