import JSP000930ActualMarkedTailTelescope

namespace JSP000930.Negative

open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA

noncomputable def closeOpenTail {d a : GroundContinuumSuccIndex} (i : OpenWetzelTail d a) :
    ClosedWetzelTail d a := ⟨i.val,i.property.1,i.property.2.le⟩

noncomputable def actualMaskedSurvivorTower {d a : GroundContinuumSuccIndex} (hd : d<a)
    (hL : CheckedGroundLimit a) (hB : ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j))
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (hSep : ∀ j,d≤j → j<a → ∀ r t : s,r≠t →
      u ≤ (labelAgreement (preparedWetzelRows r.val j) (preparedWetzelRows t.val j))ᶜ) :
    MaskedContinuousTower (actualAugmentedQ a s) (fun i : OpenWetzelTail d a => actualAugmentedQ i.val s) u where
  into i := actualAugmentedLocalArrow i.property.2.le hB s u
  shift i j hij := actualAugmentedLocalArrow hij (fun k hk => hB k (hk.trans j.property.2)) s u
  into_predense i :=
    actualTailArrow_predense hB s u hSep ⟨a,hd.le,le_rfl⟩ (closeOpenTail i) i.property.2.le
  shift_predense i j hij :=
    actualTailArrow_predense hB s u hSep (closeOpenTail j) (closeOpenTail i) hij
  coherent i j hij p := actualAugmentedIncludeLabel_comp hij j.property.2.le s p
  final_dense p := by
    obtain ⟨i,hia,hdi,q,hq⟩ := actualAugmented_earlierOnTail hd hL hB s u p
    exact ⟨⟨i,hdi,hia⟩,q,hq.le⟩
  earlier_dense j hj p := by
    obtain ⟨k,hkj⟩ := hj.1
    have hD : d<j.val := k.property.1.trans_lt hkj
    have hGap (i : GroundContinuumSuccIndex) (hi : d ≤ i) (hij : i < j.val) :
        ∃ t,i<t ∧ t<j.val := by
      obtain ⟨t,hit,htj⟩ := hj.2 ⟨i,hi,hij.trans j.property.2⟩ hij
      exact ⟨t.val,hit,htj⟩
    obtain ⟨i,hij,hdi,q,hq⟩ := actualAugmented_earlierOnTail hD (checkedLimit_of_tailGap hD hGap)
      (fun t ht => hB t (ht.trans j.property.2)) s u p
    exact ⟨⟨i,hdi,hij.trans j.property.2⟩,hij,q,hq.le⟩

end JSP000930.Negative
