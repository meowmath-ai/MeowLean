import JSP000933ActualLowGradeFiniteDifference

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualCollapseHits_null_r384 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hqp : q≤p) (hB : q≤(actualNoCollapseValue T)ᶜ) :
    LocalLE true q (actualFixtureGluing T (collapseOutputKernel T 0)) (fun _ => ⊥) := by
  let A := actualFixtureGluing T (collapseOutputKernel T 0)
  let z : ℕ → B := fun _ => ⊥
  apply nameOrder_of_positiveTails_r229
  intro k hk
  let J := 2*k
  let H := actualFixtureGluing T (collapseOutputKernel T J)
  have hJ : 2*k≤(2:ℕ)^J := (Nat.le_succ J).trans (nat_succ_le_power_two_r344 J)
  have h2 : 2*k≠0 := by omega
  let U := nameBudgetValue true (realBitsName A) (realBitsName H)
  let V := nameBudgetValue true (realBitsName H) (realBitsName z)
  have hU : q≤eventualBudgetAt U (2*k) :=
    (actualHighGradeOutput_harmEq_on_bad_r383 T hqp hB J).1.trans
      (nameOrder_positiveTails_r229 true _ _ _ h2)
  have hV : q≤eventualBudgetAt V (2*k) := by
    apply le_iSup_of_le 0
    apply budgetTail_of_forall_r229
    intro n _
    exact (hqp.trans (actualHighGradeOutput_prefixBudget_r382 T J n)).trans
      (nameBudgetValue_scale_antitone_r316 true H z n hJ)
  exact (le_inf hU hV).trans (eventualBudgetAt_binary_r290 U V _ k
    (nameBudgetValue_triangle_r228 true (realBitsName A) (realBitsName H) (realBitsName z) k))

theorem actualCollapseEval_below_hits_empty_r384 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hC : NamedContinuousOn p L) :
    p≤bitsBelowValue (actualClampedOutput T (actualFixtureGluing T (collapseSourceKernel T)))
      (bitsJoin (actualFixtureGluing T (collapseOutputKernel T 0)) (actualClampedOutput T (fun _ => ⊥))) := by
  let X := actualFixtureGluing T (collapseSourceKernel T)
  let H := actualFixtureGluing T (collapseOutputKernel T 0)
  let z : ℕ → B := fun _ => ⊥
  unfold bitsBelowValue
  apply le_iInf
  intro m
  apply (le_materialImp_iff_r126 _ _ _).mpr
  apply le_of_dense_named_refinements_r219
  intro q hq hQ
  have hqp : q≤p := hQ.trans inf_le_left
  obtain ⟨A,r,hr,hrq,hA⟩ := exists_nonzero_below_choice_r135 q hq (fixtureWeight T (m+1))
    (hqp.trans_eq (fixtureWeight_covers_r376 T (m+1)).symm)
  have hEval : r≤actualClampedOutput T X m := hrq.trans (hQ.trans inf_le_right)
  have hClamp : r≤actualBlockClamp T m := hEval.trans inf_le_right
  rcases fixture_output_at_window_or_zero_r381 T A hr hA m le_rfl with ⟨i,hW⟩ | h0
  · let D := fixtureSnapshot A i
    let a := collapsePick D (fixtureGradeAt A i.val)
    have hD := hA.trans (fixtureWeight_snapshot_r376 T A i)
    have hR : m∈D.range := prop_of_le_crisp_nonzero_r190 hr
      (((le_inf le_rfl hClamp).trans_eq (actualBlockSnapshotValue_range_r367 hD m hW)).trans inf_le_right)
    have hX (s : ℕ) (hs : s∈blockSnapshotSource D.history) : r⊓X s=r⊓crispFinsetBits a.val s :=
      actualFixtureGluing_mask_r379 T (collapseSourceKernel T) A i hA s hs
    by_cases hHit : fixtureHit A i
    · have he := snapshot_act_arbitrary_r368 hC hD X a hX m hW
      have hm := actualFixtureGluing_mask_r379 T (collapseOutputKernel T 0) A i hA m hR
      have hM : collapseMarkedOutput A 0 i=D.act a := by simp [collapseMarkedOutput,hHit,D,a]
      have hMH : r⊓H m=r⊓crispFinsetBits (D.act a) m := by
        change r⊓H m=r⊓crispFinsetBits (collapseMarkedOutput A 0 i) m at hm
        exact hm.trans (congrArg (fun V : Finset ℕ => r⊓crispFinsetBits V m) hM)
      exact ⟨r,hr,hrq,(((le_inf le_rfl hEval).trans_eq (he.trans hMH.symm)).trans inf_le_right).trans le_sup_left⟩
    · have ha : a=emptyBlockInput D.history := collapsePick_good_empty_r377 hHit
      have he (s : ℕ) (hs : s∈blockSnapshotSource D.history) : r⊓X s=r⊓z s := by
        have he := hX s hs
        rw [ha] at he
        simpa [emptyBlockInput,crispFinsetBits,crispTruth,z] using he
      have hSame := actualClampedOutput_local_r365 T hC D.history (actualBlockSnapshotValue_history_r367 hD)
        X z i.val m (by omega) hW he
      exact ⟨r,hr,hrq,(((le_inf le_rfl hEval).trans_eq hSame).trans inf_le_right).trans le_sup_right⟩
  · exact False.elim (hr (le_bot_iff.mp ((le_inf le_rfl hClamp).trans_eq h0)))

end SetLanguage
end JSP000933
