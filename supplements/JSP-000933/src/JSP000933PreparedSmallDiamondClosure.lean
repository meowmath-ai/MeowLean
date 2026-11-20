import JSP000933PreparedSmallDiamondIndices

open Cardinal Flypitch

namespace JSP000933
namespace PreparedModel

theorem smallDiamond_chain_lower_exact_r400 {I : Type} (f : I → SmallDiamondCondition)
    (hI : Cardinal.mk I<GroundContinuumSucc)
    (hC : ∀ i j, f i≤f j ∨ f j≤f i) :
    ∃ q : SmallDiamondCondition, (∀ i, q≤f i) ∧
      continuumSuccOrdinal q.length=⨆ i,continuumSuccOrdinal (f i).length := by
  classical
  let g (i : I) := continuumSuccOrdinal (f i).length
  have hIC : Cardinal.mk I<GroundContinuumSucc.ord.cof :=
    hI.trans_eq groundContinuumSucc_regular_r392.cof_ord.symm
  have hS : (⨆ i, g i)<GroundContinuumSucc.ord :=
    Ordinal.iSup_lt_of_lt_cof hIC (fun i => continuumSuccOrdinal_lt_r392 (f i).length)
  let d := continuumSuccIndexOf (⨆ i, g i) hS
  have hD : continuumSuccOrdinal d=(⨆ i,g i) := continuumSuccIndexOf_ordinal_r399 _ _
  have hLen (i : I) : (f i).length≤d :=
    (continuumSuccIndex_le_iff_r399 _ _).mpr ((Ordinal.le_iSup g i).trans_eq hD.symm)
  have hPick (a : {a : GroundContinuumSuccIndex // a<d}) : ∃ i : I, a.val<(f i).length := by
    have ha : continuumSuccOrdinal a.val<(⨆ i, g i) :=
      ((continuumSuccIndex_lt_iff_r399 _ _).mp a.property).trans_eq hD
    obtain ⟨i,hi⟩ := Ordinal.lt_iSup_iff.mp ha
    exact ⟨i,(continuumSuccIndex_lt_iff_r399 _ _).mpr hi⟩
  choose j hJ using hPick
  let q : SmallDiamondCondition :=
    ⟨d,fun a ha => (f (j ⟨a,ha⟩)).guesses a (hJ ⟨a,ha⟩),
      fun a ha b hb => (f (j ⟨a,ha⟩)).supported a (hJ ⟨a,ha⟩) b hb⟩
  refine ⟨q,(fun i => ⟨hLen i,?_⟩),hD⟩
  intro a ha
  let A : {a : GroundContinuumSuccIndex // a<d} := ⟨a,ha.trans_le (hLen i)⟩
  let k := j A
  change (f k).guesses a (hJ A)=(f i).guesses a ha
  rcases hC k i with h | h
  · exact h.2 a ha
  · exact (h.2 a (hJ A)).symm

theorem smallDiamond_chain_lower_r400 {I : Type} (f : I→SmallDiamondCondition)
    (hI : Cardinal.mk I<GroundContinuumSucc) (hC : ∀ i j,f i≤f j ∨ f j≤f i) :
    ∃ q : SmallDiamondCondition,∀ i,q≤f i := by
  obtain ⟨q,hq,_⟩ := smallDiamond_chain_lower_exact_r400 f hI hC
  exact ⟨q,hq⟩

open scoped Classical in
noncomputable def smallDiamondPad (p : SmallDiamondCondition) (d : GroundContinuumSuccIndex) :
    SmallDiamondCondition where
  length := d
  guesses a _ := if h : a<p.length then p.guesses a h else ∅
  supported a _ b hb := by
    by_cases h : a<p.length
    · exact p.supported a h b (by simpa only [dite_eq_left h] using hb)
    · simp [h] at hb

theorem smallDiamondPad_le_r400 (p : SmallDiamondCondition) (d : GroundContinuumSuccIndex)
    (h : p.length≤d) : smallDiamondPad p d≤p :=
  ⟨h,fun a ha => by simp only [smallDiamondPad,dite_eq_left ha]⟩

theorem smallDiamond_endExtend_past_r400 (p : SmallDiamondCondition) (a : GroundContinuumSuccIndex) :
    ∃ q : SmallDiamondCondition, q≤p ∧ a<q.length := by
  obtain ⟨b,hB⟩ := continuumSuccIndex_family_bounded_r399
    (fun k : Bool => if k then p.length else a)
    (by
      rw [Cardinal.mk_bool]
      exact (Cardinal.nat_lt_continuum 2).trans (Order.lt_succ _))
  have hP : p.length<b := by simpa using hB true
  have hA : a<b := by simpa using hB false
  exact ⟨smallDiamondPad p b,smallDiamondPad_le_r400 p b hP.le,hA⟩

theorem smallDiamond_append_r400 (p : SmallDiamondCondition) (G : Set GroundContinuumSuccIndex)
    (hG : ∀ b∈G,b<p.length) :
    ∃ (q : SmallDiamondCondition) (hL : p.length<q.length),
      q≤p ∧ q.guesses p.length hL=G := by
  classical
  let α := continuumSuccOrdinal p.length+1
  have hα : α<GroundContinuumSucc.ord :=
    (Cardinal.isSuccLimit_ord groundContinuumSucc_regular_r392.1).add_one_lt
      (continuumSuccOrdinal_lt_r392 p.length)
  let d := continuumSuccIndexOf α hα
  have hL : p.length<d := by
    apply (continuumSuccIndex_lt_iff_r399 _ _).mpr
    rw [continuumSuccIndexOf_ordinal_r399]
    exact Order.lt_add_one_iff.mpr le_rfl
  let w (a : GroundContinuumSuccIndex) := if h : a<p.length then p.guesses a h
    else if a=p.length then G else ∅
  have hW (a b : GroundContinuumSuccIndex) (hb : b∈w a) : b<a := by
    by_cases ha : a<p.length
    · exact p.supported a ha b (by simpa only [w,dite_eq_left ha] using hb)
    · by_cases he : a=p.length
      · have hb' : b∈G := by simpa only [w,dite_eq_right ha,ite_eq_left he] using hb
        exact (hG b hb').trans_eq he.symm
      · simp [w,ha,he] at hb
  let q : SmallDiamondCondition := ⟨d,fun a _ => w a,fun a _ b hb => hW a b hb⟩
  refine ⟨q,hL,⟨hL.le,fun a ha => ?_⟩,?_⟩
  · simp only [q,w,dite_eq_left ha]
  · simp only [q,w,dite_eq_right (lt_irrefl _),ite_true]

end PreparedModel
end JSP000933
