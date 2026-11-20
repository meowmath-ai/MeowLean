import JSP000933ActualCollapseOutputNull

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem localLE_of_bitsBelow_r385 {p : B} (h : Bool) {a b : ℕ → B} (hab : p≤bitsBelowValue a b) :
    LocalLE h p a b :=
  (LocalEq.of_realEq_r246 h (maskedMeetAbsorb_r365 hab)).2.trans_r236
    (LocalLE.meet_bounds_r237 h p b a).1

theorem actualNoCollapse_holds_r385 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x))) :
    p≤actualNoCollapseValue T := by
  by_contra hn
  let q := p⊓(actualNoCollapseValue T)ᶜ
  have hq : q≠⊥ := by
    intro h
    exact hn ((le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr h.le)).trans_eq (compl_compl _))
  have hqp : q≤p := inf_le_left
  have hB : q≤(actualNoCollapseValue T)ᶜ := inf_le_right
  let X := actualFixtureGluing T (collapseSourceKernel T)
  let H := actualFixtureGluing T (collapseOutputKernel T 0)
  let z : ℕ → B := fun _ => ⊥
  let Y := actualClampedOutput T X
  let E := actualClampedOutput T z
  have hX : p≤bitsBelowValue X (actualSourceUnion T) :=
    actualSourceFixtureGluing_below_r379 T (collapseSourceKernel T)
  have hz : p≤bitsBelowValue z (actualSourceUnion T) := bitsBelowValue_of_pointwise_r272 (fun _ => bot_le)
  let I := F.restrict_r246 hqp
  have he : LocalEq true q E (F.toName z) :=
    (actualClampedOutput_harmEq_r364 F T hL z hz).of_stronger_r246 hqp
  have hFz : LocalEq true q (F.toName z) z := I.mapBot_r237
  have hE : LocalLE true q E z := he.1.trans_r236 hFz.1
  have hH : LocalLE true q H z := actualCollapseHits_null_r384 T hqp hB
  have hHE : LocalLE true q (bitsJoin H E) z := LocalLE.join_left_r236.mpr ⟨hH,hE⟩
  have hA : LocalLE true q Y z :=
    (localLE_of_bitsBelow_r385 true (hqp.trans (actualCollapseEval_below_hits_empty_r384 T hC))).trans_r236 hHE
  have hFY : LocalLE true q (F.toName X) Y :=
    ((actualClampedOutput_harmEq_r364 F T hL X hX).of_stronger_r246 hqp).2
  have hOrd : LocalLE false q X z := (I.order X z).mpr (hFY.trans_r236 (hA.trans_r236 hFz.2))
  let U := nameBudgetValue false (realBitsName X) (realBitsName z)
  have hT : q≤⨆ N, budgetTail U 4 N :=
    hOrd.trans (nameOrder_positiveTails_r229 false _ _ 4 (by decide))
  obtain ⟨N,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (budgetTail U 4) hT
  obtain ⟨M,A,i,s,hs,hsr,hSA,hi,hHit⟩ := exists_actualLateHit_refinement_r378 T hr
    (hrq.trans hqp) (hrq.trans hB) N
  let D := fixtureSnapshot A i
  let a := collapsePick D (fixtureGradeAt A i.val)
  have hBadPiece : ¬GroundAllBudgets false 4 a.val := (collapsePick_bad_spec_r377 hHit).1
  have hD := hSA.trans (fixtureWeight_snapshot_r376 T A i)
  have hIn (m : ℕ) (hm : m∈a.val) : s≤X m := by
    have hM : m∈blockSnapshotSource D.history := Finset.mem_powerset.mp a.property hm
    have he := actualFixtureGluing_mask_r379 T (collapseSourceKernel T) A i hSA m hM
    have hX' : s⊓X m=s := by
      change s⊓X m=s⊓crispFinsetBits a.val m at he
      simpa [crispFinsetBits,crispTruth,hm] using he
    exact hX'.symm.le.trans inf_le_right
  have hLate (m : ℕ) (hm : m∈a.val) : N≤ m :=
    hi.trans ((sourceSnapshotCarrier T).ge_index i.val D s hs hD m (Finset.mem_powerset.mp a.property hm))
  apply hBadPiece
  exact groundAllBudgets_from_namedTail_r374 hs false 4 N X a.val hIn hLate (hsr.trans hR)

end SetLanguage
end JSP000933
