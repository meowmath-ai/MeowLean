import JSP000933PreparedNameCodes

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

def markedGuess (d z : GroundContinuumSuccIndex) (q : SmallDiamondCondition) : Prop :=
  ∃ h : d<q.length,z∈q.guesses d h

noncomputable def preparedGuessBit (d z : GroundContinuumSuccIndex) : PreparedBA :=
  ⨆ p : {p : PreparedCondition // markedGuess d z p.2},imageCondition p.val

theorem preparedGuessBit_of_yes_r407 (p : PreparedCondition) {d z : GroundContinuumSuccIndex}
    (hd : d<p.2.length) (hz : z∈p.2.guesses d hd) :
    imageCondition p≤preparedGuessBit d z :=
  le_iSup (fun q : {q : PreparedCondition // markedGuess d z q.2} => imageCondition q.val) ⟨p,hd,hz⟩

theorem preparedGuessBit_of_no_r407 (p : PreparedCondition) {d z : GroundContinuumSuccIndex}
    (hd : d<p.2.length) (hz : z∉p.2.guesses d hd) :
    imageCondition p⊓preparedGuessBit d z=⊥ := by
  apply le_bot_iff.mp
  rw [preparedGuessBit,inf_iSup_eq]
  apply iSup_le
  intro q
  apply disjoint_iff_inf_le.mp
  by_contra h
  obtain ⟨r,hrp,hrq⟩ := (compatible_iff_not_disjoint_r50 p q.val).mpr h
  obtain ⟨hq,hQ⟩ := q.property
  have hp' : r.2.guesses d (hd.trans_le hrp.2.1)=p.2.guesses d hd := hrp.2.2 d hd
  have hq' : r.2.guesses d (hq.trans_le hrq.2.1)=q.val.2.guesses d hq := hrq.2.2 d hq
  exact hz (hp' ▸ (hq'.symm ▸ hQ))

noncomputable def decodePreparedGuess (d i : GroundContinuumSuccIndex) : PreparedBA :=
  ⨆ r : CollapseBasicCondition,
    preparedGuessBit d (collapseNameCode (r,i))⊓embedCollapse (basicValue r)

theorem preparedGuess_assigned_r407 (p : PreparedCondition)
    (s : SmallDiamondCondition) (A : GroundContinuumSuccIndex→PreparedBA)
    (d i : GroundContinuumSuccIndex) (hd : d<p.2.length) (hi : i<d)
    (hG : p.2.guesses d hd=encodeProfile s A d) :
    imageCondition p⊓decodePreparedGuess d i=
      imageCondition p⊓embedCollapse (decodeCut (positiveCut s (A i))) := by
  classical
  have hMap : embedCollapse (decodeCut (positiveCut s (A i)))=
      ⨆ r : positiveCut s (A i),embedCollapse (basicValue r.val) :=
    embedCollapse_joins_r403 _
  simp only [decodePreparedGuess,hMap,inf_iSup_eq]
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hr : r∈positiveCut s (A i)
    · apply le_iSup_of_le ⟨r,hr⟩
      exact inf_le_inf_left _ inf_le_right
    · have hN : collapseNameCode (r,i)∉p.2.guesses d hd := by
        rw [hG,code_mem_encodeProfile_r406 s A hi]
        exact hr
      rw [← inf_assoc,preparedGuessBit_of_no_r407 p hd hN,bot_inf_eq]
      exact bot_le
  · apply iSup_le
    intro r
    apply le_iSup_of_le r.val
    have hY : collapseNameCode (r.val,i)∈p.2.guesses d hd := by
      rw [hG,code_mem_encodeProfile_r406 s A hi]
      exact r.property
    have h : imageCondition p≤preparedGuessBit d (collapseNameCode (r.val,i)) :=
      preparedGuessBit_of_yes_r407 p hd hY
    rw [← inf_assoc,inf_eq_left.mpr h]

theorem booleanAgree_congr_right_r407 {m a b c : PreparedBA}
    (h : m≤booleanAgree a b) (he : m⊓b=m⊓c) : m≤booleanAgree a c := by
  change m≤(a⇨c)⊓(c⇨a)
  have h1 : m⊓a≤b := le_himp_iff.mp (h.trans inf_le_left)
  have h2 : m⊓b≤a := le_himp_iff.mp (h.trans inf_le_right)
  have h3 : m⊓a≤ m⊓b := le_inf inf_le_left h1
  exact le_inf (le_himp_iff.mpr ((h3.trans_eq he).trans inf_le_right))
    (le_himp_iff.mpr (he.symm.trans_le h2))

end PreparedModel
end JSP000933
