import JSP000933PreparedMixedClubFusion

open Cardinal

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

def OmegaOneCofinalIndex (d : GroundContinuumSuccIndex) : Prop :=
  (continuumSuccOrdinal d).cof=ℵ₁

theorem exists_prepared_actualDiamond_r410 (A C : GroundContinuumSuccIndex→PreparedBA)
    (mark : PreparedBA) (hU : ∀ a,mark≤aboveClub C a)
    (hC : ∀ d,OmegaOneCofinalIndex d → mark⊓clubAccumulation C d≤C d)
    (p : PreparedCondition) (hP : imageCondition p ≤ mark) :
    ∃ (out : PreparedCondition) (d : GroundContinuumSuccIndex),
      out≤p ∧ OmegaOneCofinalIndex d ∧ imageCondition out≤C d ∧
      ∀ i<d,imageCondition out≤booleanAgree (A i) (decodePreparedGuess d i) := by
  classical
  let lamOrd : Ordinal := (ℵ₁ : Cardinal).ord
  let I := lamOrd.ToType
  let e := Ordinal.ToType.mk (o := lamOrd)
  have hLim : Order.IsSuccLimit lamOrd := Cardinal.isSuccLimit_ord Cardinal.isRegular_aleph_one.1
  letI : Nonempty I := Ordinal.nonempty_toType_iff.mpr (ne_of_gt hLim.pos)
  letI : NoMaxOrder I := ⟨fun i => by
    let a := e.symm i
    let b : ↥(Set.Iio lamOrd) := ⟨a.val+1,hLim.add_one_lt a.property⟩
    have hab : a<b := by
      change a.val < a.val + 1
      exact Order.lt_add_one_iff.mpr le_rfl
    have ht := e.strictMono hab
    change e (e.symm i) < e b at ht
    rw [e.apply_symm_apply i] at ht
    exact ⟨e b,ht⟩⟩
  have hI : Cardinal.mk I<GroundContinuumSucc := by
    change Cardinal.mk (ℵ₁ : Cardinal).ord.ToType<GroundContinuumSucc
    rw [Cardinal.mk_toType,Cardinal.card_ord]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  obtain ⟨f,g,h0,hEarlier,hStep⟩ := exists_preparedFusionStages_r409
    (I := I) hI A C mark hU p.1 p.2 hP
  have hChain (i j : I) : g i≤g j ∨ g j≤g i := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact Or.inr ((hStep j).stronger.trans (hEarlier j i h))
    · exact Or.inl le_rfl
    · exact Or.inl ((hStep i).stronger.trans (hEarlier i j h))
  obtain ⟨s,hs,hOrd⟩ := smallDiamond_chain_lower_exact_r400 g hI hChain
  let d := s.length
  let lens (i : I) := continuumSuccOrdinal (g i).length
  have hLens : StrictMono lens := by
    intro i j hij
    apply (continuumSuccIndex_lt_iff_r399 _ _).mp
    exact (SmallDiamondCondition.length_mono_r399 (hEarlier j i hij)).trans_lt (hStep j).longer
  have hdCof : OmegaOneCofinalIndex d := by
    change (continuumSuccOrdinal s.length).cof=ℵ₁
    rw [hOrd,Ordinal.cof_iSup hLens]
    change Order.cof lamOrd.ToType=ℵ₁
    rw [← Ordinal.cof_type,Ordinal.type_toType,Cardinal.isRegular_aleph_one.cof_ord]
  let i0 : I := Classical.choice inferInstance
  have hsP : s≤p.2 := (hs i0).trans ((hStep i0).stronger.trans (h0 i0))
  have hAt (a : GroundContinuumSuccIndex) (ha : a<d) : ∃ j : I,a<(f j).length := by
    have hap : continuumSuccOrdinal a<⨆ j,lens j :=
      ((continuumSuccIndex_lt_iff_r399 _ _).mp ha).trans_eq hOrd
    obtain ⟨i,hi⟩ := Ordinal.lt_iSup_iff.mp hap
    obtain ⟨j,hij⟩ := exists_gt i
    exact ⟨j,((continuumSuccIndex_lt_iff_r399 _ _).mpr hi).trans_le
      (SmallDiamondCondition.length_mono_r399 (hEarlier j i hij))⟩
  have hCode : codeClosedAt d := by
    intro r i hi
    obtain ⟨j,hj⟩ := hAt i hi
    exact ((hStep j).codes r i hj).trans_le (SmallDiamondCondition.length_mono_r399 (hs j))
  have hAcc : imageCondition ((p.1,s) : PreparedCondition)≤clubAccumulation C d := by
    apply le_iInf
    intro a
    obtain ⟨j,hj⟩ := hAt a.val a.property
    exact ((imageCondition_mono_r50 (show ((p.1,s) : PreparedCondition)≤(p.1,g j)
      from ⟨le_rfl,hs j⟩)).trans (hStep j).seesClub).trans
      (clubWindow_mono_r408 C hj.le (SmallDiamondCondition.length_mono_r399 (hs j)))
  have hCδ : imageCondition ((p.1,s) : PreparedCondition)≤C d :=
    (le_inf ((imageCondition_mono_r50 (show ((p.1,s) : PreparedCondition)≤p from
      ⟨le_rfl,hsP⟩)).trans hP) hAcc).trans (hC d hdCof)
  obtain ⟨t,htLen,ht,htGuess⟩ := smallDiamond_append_r400 s (encodeProfile s A d)
    (encodeProfile_supported_r406 s A d hCode)
  let out : PreparedCondition := (p.1,t)
  have hout : out≤(p.1,s) := ⟨le_rfl,ht⟩
  refine ⟨out,d,⟨le_rfl,ht.trans hsP⟩,hdCof,
    (imageCondition_mono_r50 hout).trans hCδ,fun i hi => ?_⟩
  obtain ⟨j,hj⟩ := hAt i hi
  have hD := (hStep j).decisions s (hs j) i hj
  have hEqual := preparedGuess_assigned_r407 out s A d i htLen hi htGuess
  exact booleanAgree_congr_right_r407 ((imageCondition_mono_r50 hout).trans hD) hEqual.symm

noncomputable def preparedCorrectGuessValue (A C : GroundContinuumSuccIndex→PreparedBA) :
    PreparedBA :=
  ⨆ d : {d : GroundContinuumSuccIndex // OmegaOneCofinalIndex d},
    C d.val⊓⨅ i : ↥(Set.Iio d.val),booleanAgree (A i.val) (decodePreparedGuess d.val i.val)

theorem prepared_actualDiamond_value_r410 (A C : GroundContinuumSuccIndex→PreparedBA)
    (mark : PreparedBA) (hU : ∀ a,mark≤aboveClub C a)
    (hC : ∀ d,OmegaOneCofinalIndex d → mark⊓clubAccumulation C d≤C d) :
    mark≤preparedCorrectGuessValue A C := by
  classical
  let v := preparedCorrectGuessValue A C
  change mark ≤ v
  by_contra hn
  have hWrong : mark⊓vᶜ≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨p,hP⟩ := imageCondition_dense_r50 _ hWrong
  obtain ⟨out,d,ho,hd,hClub,hGuesses⟩ := exists_prepared_actualDiamond_r410
    A C mark hU hC p (hP.trans inf_le_left)
  have hYes : imageCondition out≤v :=
    le_iSup_of_le ⟨d,hd⟩ (le_inf hClub (le_iInf (fun i => hGuesses i.val i.property)))
  have hNo : imageCondition out≤vᶜ :=
    (imageCondition_mono_r50 ho).trans (hP.trans inf_le_right)
  exact imageCondition_ne_bot_r50 out (disjoint_compl_right.out _ hYes hNo)

end PreparedModel
end JSP000933
