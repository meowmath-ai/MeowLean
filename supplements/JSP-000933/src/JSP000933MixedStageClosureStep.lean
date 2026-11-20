import JSP000933LocalKappaTraceSupport
import JSP000933PreparedMixedClubStep

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel BooleanCompletion

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def mixedClosedStageValue
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B) (d : GroundContinuumSuccIndex) : B :=
  ⨅ i : ↥(Set.Iio d),⨆ b : ↥(Set.Iio d),F i.val b.val

noncomputable def kappaClubAccumulation
    (C : GroundContinuumSuccIndex→B) (d : GroundContinuumSuccIndex) : B :=
  ⨅ a : ↥(Set.Iio d),⨆ b : {b : GroundContinuumSuccIndex // a.val<b ∧ b<d},C b.val

theorem mixedClosedStage_closed_r481
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B) (d : GroundContinuumSuccIndex) :
    kappaClubAccumulation (mixedClosedStageValue F) d ≤ mixedClosedStageValue F d := by
  apply le_iInf
  intro i
  apply (iInf_le _ i).trans
  apply iSup_le
  intro j
  unfold mixedClosedStageValue
  apply (iInf_le _ (⟨i.val,j.property.1⟩ : ↥(Set.Iio j.val))).trans
  apply iSup_le
  intro b
  exact le_iSup (fun k : ↥(Set.Iio d) => F i.val k.val) ⟨b.val,b.property.trans j.property.2⟩

set_option maxHeartbeats 450000 in
theorem exists_mixedClosedStage_step_r481 {P : Type} [Preorder P]
    (hB : BoundsSmallKappaNames (RO P))
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→RO P)
    (hF : ∀ i,(⨆ b,F i b)=⊤)
    (p : P) (a : GroundContinuumSuccIndex) :
    ∃ (q : P) (d : GroundContinuumSuccIndex),q≤p ∧ a<d ∧
      ∀ i<a,imageCondition q≤⨆ b : ↥(Set.Iio d),F i b.val := by
  let I := ↥(Set.Iio a)
  let V (i : I) (b : GroundContinuumSuccIndex) := F i.val b
  let X (b : GroundContinuumSuccIndex) := ⨅ i : I,⨆ j : ↥(Set.Iio b),V i j.val
  have hAll : (⊤ : RO P) ≤ ⨅ i : I, ⨆ b : GroundContinuumSuccIndex, V i b := by
    apply le_iInf
    intro i
    exact (hF i.val).ge
  have hTop : (⨆ b,X b)=⊤ :=
    top_unique (hAll.trans (hB I (continuumSuccInitial_card_lt_r406 a) V))
  have hP : imageCondition p≤⨆ b,X b := hTop.symm ▸ le_top
  obtain ⟨c,q,hq,hVal⟩ := exists_stronger_below_indexedSup_r51 p X hP
  have hBool : Cardinal.mk Bool < GroundContinuumSucc := by
    rw [Cardinal.mk_bool]
    exact (Cardinal.nat_lt_continuum 2).trans (Order.lt_succ Cardinal.continuum)
  obtain ⟨d,hd⟩ := continuumSuccIndex_family_bounded_r399 (fun j : Bool => if j then a else c) hBool
  have ha : a<d := by simpa using hd true
  have hc : c<d := by simpa using hd false
  refine ⟨q,d,hq,ha,fun i hi => ?_⟩
  have hSmall : imageCondition q ≤ ⨆ b : ↥(Set.Iio c), F i b.val :=
    hVal.trans (iInf_le (fun j : I => ⨆ b : ↥(Set.Iio c), V j b.val) ⟨i,hi⟩)
  apply hSmall.trans
  apply iSup_le
  intro b
  exact le_iSup (fun k : ↥(Set.Iio d) => F i k.val) ⟨b.val,b.property.trans hc⟩

end RelativeOCA
end JSP000933
