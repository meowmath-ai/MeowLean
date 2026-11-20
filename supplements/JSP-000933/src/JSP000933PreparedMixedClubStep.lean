import JSP000933PreparedGuessDecoding

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

noncomputable def aboveClub (C : GroundContinuumSuccIndex→PreparedBA) (a : GroundContinuumSuccIndex) :
    PreparedBA := ⨆ j : {j : GroundContinuumSuccIndex // a<j},C j.val

noncomputable def inClubWindow (C : GroundContinuumSuccIndex→PreparedBA)
    (a d : GroundContinuumSuccIndex) : PreparedBA :=
  ⨆ j : {j : GroundContinuumSuccIndex // a<j ∧ j<d},C j.val

noncomputable def clubAccumulation (C : GroundContinuumSuccIndex→PreparedBA)
    (d : GroundContinuumSuccIndex) : PreparedBA :=
  ⨅ a : ↥(Set.Iio d),inClubWindow C a.val d

theorem clubWindow_mono_r408 (C : GroundContinuumSuccIndex→PreparedBA)
    {a a' d d' : GroundContinuumSuccIndex} (ha : a'≤a) (hd : d≤d') :
    inClubWindow C a d≤ inClubWindow C a' d' := by
  apply iSup_le
  intro j
  exact le_iSup (fun k : {k : GroundContinuumSuccIndex // a' < k ∧ k < d'} => C k.val)
    ⟨j.val,ha.trans_lt j.property.1,j.property.2.trans_le hd⟩

structure PreparedFusionStep (A C : GroundContinuumSuccIndex→PreparedBA)
    (p : CollapseBasicCondition) (start q : SmallDiamondCondition) : Prop where
  stronger : q ≤ start
  longer : start.length<q.length
  codes : ∀ r : CollapseBasicCondition,∀ i<start.length,collapseNameCode (r,i)<q.length
  seesClub : imageCondition ((p,q) : PreparedCondition)≤ inClubWindow C start.length q.length
  decisions : ∀ s≤q,∀ i<start.length,imageCondition ((p,s) : PreparedCondition)≤
    booleanAgree (A i) (embedCollapse (decodeCut (positiveCut s (A i))))

theorem exists_preparedFusionStep_r408 (A C : GroundContinuumSuccIndex→PreparedBA)
    (mark : PreparedBA)
    (hU : ∀ a,mark≤aboveClub C a)
    (p : CollapseBasicCondition) (start : SmallDiamondCondition)
    (hM : imageCondition ((p,start) : PreparedCondition) ≤ mark) :
    ∃ q : SmallDiamondCondition,PreparedFusionStep A C p start q := by
  let a := start.length
  let J := {j : GroundContinuumSuccIndex // a<j}
  have hUnit : Cardinal.mk (Fin 1)<GroundContinuumSucc := by
    exact ((Cardinal.mk_fin 1).trans_le Cardinal.one_le_aleph0).trans_lt
      (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
  have hTotal (_ : Fin 1) : imageCondition ((p,start) : PreparedCondition)≤⨆ j : J,C j.val :=
    hM.trans (hU a)
  obtain ⟨s,b,hs,hsC⟩ := prepared_totalProfiles_shortened_r404 hUnit
    (fun j : J => j.val) (fun (_ : Fin 1) (j : J) => C j.val) p start hTotal
  have hClub : imageCondition ((p,s) : PreparedCondition)≤ inClubWindow C a b := by
    apply (hsC 0).trans
    apply iSup_le
    intro j
    exact le_iSup (fun k : {k : GroundContinuumSuccIndex // a < k ∧ k < b} => C k.val)
      ⟨j.val.val,j.val.property,j.property⟩
  obtain ⟨t,ht,htD⟩ := prepared_shortProfiles_decoded_r405
    (continuumSuccInitial_card_lt_r406 a) (fun i : ↥(Set.Iio a) => A i.val) p s
  obtain ⟨c,hc⟩ := collapseNameCode_bounded_r406 a
  let M := max a (max b c)
  obtain ⟨q,hq,hL⟩ := smallDiamond_endExtend_past_r400 t M
  have hA : a<q.length := (le_max_left a _).trans_lt hL
  have hB : b<q.length := ((le_max_left b c).trans (le_max_right a _)).trans_lt hL
  have hC : c<q.length := ((le_max_right b c).trans (le_max_right a _)).trans_lt hL
  refine ⟨q,⟨hq.trans (ht.trans hs),hA,fun r i hi => (hc r i hi).trans hC,?_,
    fun u hu i hi => htD u (hu.trans hq) ⟨i,hi⟩⟩⟩
  have hQS : ((p,q) : PreparedCondition)≤(p,s) := ⟨le_rfl,hq.trans ht⟩
  exact ((imageCondition_mono_r50 hQS).trans hClub).trans
    (clubWindow_mono_r408 C le_rfl hB.le)

end PreparedModel
end JSP000933
