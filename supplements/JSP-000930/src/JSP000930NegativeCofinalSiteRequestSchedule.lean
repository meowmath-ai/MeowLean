import JSP000930NegativeActualBulkReservoir
import JSP000930NegativeCheckedKappaCutTraceWeights

open Cardinal

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.RelativeOCA

theorem exists_cofinalSiteRequestSchedule :
    ∃ pick : KappaSiteIndex → KappaSiteIndex,
      ∀ (request bound : KappaSiteIndex), ∃ j, bound < j ∧ pick j = request := by
  classical
  have hK : (ℵ₀ : Cardinal) ≤ GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have he : Nonempty (KappaSiteIndex ≃ KappaSiteIndex × KappaSiteIndex) := by
    apply Cardinal.eq.mp
    simp only [KappaSiteIndex,Cardinal.mk_prod,Cardinal.lift_id,continuumSuccIndex_card_r406]
    exact (Cardinal.mul_eq_left hK le_rfl (ne_of_gt (Cardinal.aleph0_pos.trans_le hK))).symm
  obtain ⟨E⟩ := he
  refine ⟨fun j => (E j).1,?_⟩
  intro req a
  by_contra h
  let f (i : KappaSiteIndex) : ClosedKappaCut a :=
    ⟨E.symm (req,i),le_of_not_gt (fun hi =>
      h ⟨E.symm (req,i),hi,congrArg Prod.fst (E.apply_symm_apply (req,i))⟩)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' := E.symm.injective (congrArg Subtype.val hij)
    exact congrArg Prod.snd h'
  have hc := (Cardinal.mk_le_of_injective hf).trans (closedKappaCut_card a)
  rw [continuumSuccIndex_card_r406] at hc
  exact (Order.lt_succ (𝔠 : Cardinal)).not_ge hc

end JSP000930.Negative
