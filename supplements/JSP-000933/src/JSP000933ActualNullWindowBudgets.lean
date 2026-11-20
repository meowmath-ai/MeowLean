import JSP000933ActualFinitePieceGluing

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def GroundAllBudgets (h : Bool) (k : ℕ) (D : Finset ℕ) : Prop :=
  ∀ n : ℕ, GroundBudgetHolds h (D : Set ℕ) ∅ k n

noncomputable def snapshotPieceGoodValue {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (h : Bool) (k j : ℕ)
    (P : ActualBlockSnapshot j → Finset ℕ) : B :=
  ⨆ D : ActualBlockSnapshot j, actualBlockSnapshotValue T j D⊓crispTruth B (GroundAllBudgets h k (P D))

noncomputable def eventuallyStageValue (G : ℕ → B) : B :=
  ⨆ N : ℕ, ⨅ j : {j : ℕ // N≤j}, G j.val

theorem groundBudget_from_namedContaining_r370 {q : B} (hq : q≠⊥)
    (h : Bool) (k n : ℕ) (a : ℕ → B) (D : Finset ℕ)
    (hD : ∀ m∈D, q≤a m)
    (hA : q≤nameBudgetValue h (realBitsName a) (realBitsName (fun _ => ⊥)) k n) :
    GroundBudgetHolds h (D : Set ℕ) ∅ k n := by
  obtain ⟨A,C,r,hr,hrq,hU,hV⟩ := exists_joint_crispPrefix_r362 a (fun _ : ℕ => (⊥ : B)) n q hq
  have hC (m : ℕ) (hm : m<n) : r⊓(⊥ : B)=r⊓crispTruth B (m∈(∅ : Set ℕ)) := by simp [crispTruth]
  have hB := (le_inf le_rfl (hrq.trans hA)).trans_eq
    (nameBudgetValue_crispPrefix_mask_r340 h k n hU hC)
  have hG : GroundBudgetHolds h A ∅ k n :=
    prop_of_le_crisp_nonzero_r190 hr (hB.trans inf_le_right)
  rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty] at hG ⊢
  apply (Nat.mul_le_mul_left _ (groundBudgetMass_prefix_mono_r341 h n ?_)).trans hG
  intro m hm hM
  have hx : r≤a m := hrq.trans (hD m hM)
  exact prop_of_le_crisp_nonzero_r190 hr
    (((le_inf le_rfl hx).trans_eq (hU m hm)).trans inf_le_right)

theorem namedNull_containedSnapshot_eventuallyBudget_r370 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (C : SnapshotCarrier T) (h : Bool) (k : ℕ) (hk : k≠0)
    (a : ℕ → B) (hA : LocalLE h p a (fun _ => ⊥))
    (P : ∀ j, ActualBlockSnapshot j → Finset ℕ) (hP : ∀ j D, P j D⊆C.bits j D)
    (hInc : ∀ j D m, m∈P j D → actualBlockSnapshotValue T j D≤a m) :
    p≤eventuallyStageValue (fun j => snapshotPieceGoodValue T h k j (P j)) := by
  have hT : p≤⨆ N, budgetTail (nameBudgetValue h (realBitsName a) (realBitsName (fun _ => ⊥))) k N :=
    hA.trans (nameOrder_positiveTails_r229 h _ _ k hk)
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨N,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq _ (hqp.trans hT)
  refine ⟨r,hr,hrq,le_iSup_of_le N ?_⟩
  apply le_iInf
  intro j
  apply le_of_dense_named_refinements_r219
  intro s hs hsr
  have hsP := hsr.trans (hrq.trans hqp)
  obtain ⟨D,t,ht,hts,hD⟩ := exists_nonzero_below_choice_r135 s hs (actualBlockSnapshotValue T j.val)
    (hsP.trans (actualBlockSnapshots_cover_r366 T j.val))
  have hG : GroundAllBudgets h k (P j.val D) := by
    intro n
    by_cases hn : N≤n
    · exact groundBudget_from_namedContaining_r370 ht h k n a (P j.val D)
        (fun m hm => hD.trans (hInc j.val D m hm))
        (hts.trans (hsr.trans (hR.trans (budgetTail_apply_r229 _ k N n hn))))
    · rw [groundBudgetHolds_weighted_r232,Set.sdiff_empty]
      have h0 : groundBudgetMass h n (P j.val D : Set ℕ)=0 := by
        unfold groundBudgetMass
        apply Finset.sum_eq_zero
        intro m hm
        have hm_not : m∉P j.val D := by
          intro hm'
          exact hn (j.property.trans ((C.ge_index j.val D t ht hD m (hP j.val D hm')).trans
            (Finset.mem_range.mp hm).le))
        simp [hm_not]
      simp [h0]
  have hB : t≤crispTruth B (GroundAllBudgets h k (P j.val D)) := by simp [crispTruth,hG]
  exact ⟨t,ht,hts,le_iSup_of_le D (le_inf hD hB)⟩

end SetLanguage
end JSP000933
