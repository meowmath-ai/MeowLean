import JSP000933MixedStageClosureStep
import JSP000933PreparedNameCodedDiamond

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel BooleanCompletion

theorem exists_mixedClosedStage_after_r482 {P : Type} [Preorder P]
    (hP : IsCountablyClosed P) (hB : BoundsSmallKappaNames (RO P))
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→RO P)
    (hF : ∀ i,(⨆ b,F i b)=⊤) (p : P) (a : GroundContinuumSuccIndex) :
    ∃ (q : P) (d : GroundContinuumSuccIndex),q≤p ∧ a<d ∧
      imageCondition q ≤ mixedClosedStageValue F d := by
  classical
  have hStep (p : P) (a : GroundContinuumSuccIndex) :=
    exists_mixedClosedStage_step_r481 hB F hF p a
  choose q b hQP hAB hBit using hStep
  let state : ℕ→P×GroundContinuumSuccIndex :=
    Nat.rec (p,a) (fun _ t => (q t.1 t.2,b t.1 t.2))
  let r (n : ℕ) := (state n).1
  let c (n : ℕ) := (state n).2
  have hR (n : ℕ) : r (n+1)≤r n := hQP (r n) (c n)
  have hC (n : ℕ) : c n<c (n+1) := hAB (r n) (c n)
  let o (n : ℕ) := continuumSuccOrdinal (c n)
  have hSmall : Cardinal.mk ℕ<GroundContinuumSucc.ord.cof := by
    rw [groundContinuumSucc_regular_r392.cof_ord,Cardinal.mk_nat]
    exact Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _)
  have hOrd : (⨆ n,o n)<GroundContinuumSucc.ord :=
    Ordinal.iSup_lt_of_lt_cof hSmall (fun n => continuumSuccOrdinal_lt_r392 (c n))
  let d := continuumSuccIndexOf (⨆ n,o n) hOrd
  have hd : continuumSuccOrdinal d=⨆ n,o n := continuumSuccIndexOf_ordinal_r399 _ _
  have hCd (n : ℕ) : c n≤d :=
    (continuumSuccIndex_le_iff_r399 _ _).mpr ((Ordinal.le_iSup o n).trans_eq hd.symm)
  obtain ⟨s,hs⟩ := hP r (antitone_nat_of_succ_le hR)
  refine ⟨s,d,hs 0,(hC 0).trans_le (hCd 1),?_⟩
  apply le_iInf
  intro i
  have hi : continuumSuccOrdinal i.val<(⨆ n,o n) :=
    ((continuumSuccIndex_lt_iff_r399 _ _).mp i.property).trans_eq hd
  obtain ⟨n,hn⟩ := Ordinal.lt_iSup_iff.mp hi
  have hn' : i.val<c n := (continuumSuccIndex_lt_iff_r399 _ _).mpr hn
  have hS : imageCondition s≤⨆ j : ↥(Set.Iio (c (n+1))),F i.val j.val :=
    (imageCondition_mono_r50 (hs (n+1))).trans (hBit (r n) (c n) i.val hn')
  apply hS.trans
  exact iSup_le (fun j => le_iSup (fun k : ↥(Set.Iio d) => F i.val k.val)
    ⟨j.val,j.property.trans_le (hCd (n+1))⟩)

theorem mixedClosedStage_unbounded_r482 {P : Type} [Preorder P]
    (hP : IsCountablyClosed P) (hB : BoundsSmallKappaNames (RO P))
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→RO P)
    (hF : ∀ i,(⨆ b,F i b)=⊤) (a : GroundContinuumSuccIndex) :
    (⊤ : RO P)≤aboveKappaValue (mixedClosedStageValue F) a := by
  classical
  let w := aboveKappaValue (mixedClosedStageValue F) a
  by_contra hn
  have hN : wᶜ≠⊥ := fun he => hn (compl_eq_bot.mp he).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
  obtain ⟨q,d,hq,hd,hD⟩ := exists_mixedClosedStage_after_r482 hP hB F hF p a
  have hW : imageCondition q≤w := hD.trans (le_iSup
    (fun j : {j : GroundContinuumSuccIndex // a < j} => mixedClosedStageValue F j.val) ⟨d,hd⟩)
  exact imageCondition_ne_bot_r50 q
    (disjoint_compl_right.out _ hW ((imageCondition_mono_r50 hq).trans hp))

theorem prepared_diamondOnMixedClosedStages_r482 (A : GroundContinuumSuccIndex→PreparedBA)
    (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→PreparedBA)
    (hF : ∀ i,(⨆ b,F i b)=⊤) :
    (⊤ : PreparedBA)≤preparedCorrectGuessValue A (mixedClosedStageValue F) := by
  apply prepared_actualDiamond_value_r410 A (mixedClosedStageValue F) ⊤
  · exact mixedClosedStage_unbounded_r482 preparedProduct_countablyClosed_r401
      actual_prepared_boundsSmallKappa_r473 F hF
  · intro d _
    rw [top_inf_eq]
    exact mixedClosedStage_closed_r481 F d

end RelativeOCA
end JSP000933
