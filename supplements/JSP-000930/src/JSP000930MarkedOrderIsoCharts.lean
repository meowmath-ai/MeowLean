import JSP000930IndependentActiveMarkedPredensity

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport

variable {B C N M : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

structure WeightedPosetChart (P : ValuedPoset B N) (Q : ValuedPoset C M) where
  values : B ≃o C
  label : N ≃ M
  valid : ∀ p,values (P.valid p) = Q.valid (label p)
  refines : ∀ p q,values (P.refines p q) = Q.refines (label p) (label q)

def WeightedPosetChart.totalIso {P : ValuedPoset B N} {Q : ValuedPoset C M}
    (F : WeightedPosetChart P Q) : TotalCondition P ≃o TotalCondition Q where
  toFun p := ⟨F.values p.mask,F.label p.trace,
    fun he => p.nonzero (F.values.injective (he.trans F.values.map_bot.symm)),
    (F.values.monotone p.valid).trans_eq (F.valid _)⟩
  invFun q := ⟨F.values.symm q.mask,F.label.symm q.trace,
    fun he => q.nonzero (F.values.symm.injective (he.trans F.values.symm.map_bot.symm)),by
      apply F.values.le_iff_le.mp
      rw [F.values.apply_symm_apply,F.valid,F.label.apply_symm_apply]
      exact q.valid⟩
  left_inv p := totalCondition_eq_of_data _ _ (F.values.symm_apply_apply _) (F.label.symm_apply_apply _)
  right_inv q := totalCondition_eq_of_data _ _ (F.values.apply_symm_apply _) (F.label.apply_symm_apply _)
  map_rel_iff' := by
    intro p q
    change (F.values p.mask≤F.values q.mask ∧
      F.values p.mask≤Q.refines (F.label p.trace) (F.label q.trace)) ↔
      (p.mask≤q.mask ∧ p.mask≤P.refines p.trace q.trace)
    rw [← F.refines,F.values.le_iff_le,F.values.le_iff_le]

def WeightedPosetChart.maskedIso {P : ValuedPoset B N} {Q : ValuedPoset C M}
    (F : WeightedPosetChart P Q) (m : B) :
    MaskedCondition P m ≃o MaskedCondition Q (F.values m) where
  toFun p := ⟨F.totalIso p.val,F.values.monotone p.property⟩
  invFun q := ⟨F.totalIso.symm q.val,by
    change F.values.symm q.val.mask ≤ m
    apply F.values.le_iff_le.mp
    rw [F.values.apply_symm_apply]
    exact q.property⟩
  left_inv p := Subtype.ext (F.totalIso.symm_apply_apply p.val)
  right_inv q := Subtype.ext (F.totalIso.apply_symm_apply q.val)
  map_rel_iff' := F.totalIso.le_iff_le

theorem presPred_of_orderIso930 {P Q : Type} [Preorder P] [Preorder Q] (F : P ≃o Q) :
    PreservesPredensity F := by
  intro X hX q
  obtain ⟨p,hp,hpX⟩ := hX (F.symm q)
  have hq : F p ≤ q := (F.monotone hp).trans_eq (F.apply_symm_apply q)
  exact ⟨p,hpX,F p,hq,le_rfl⟩

end JSP000930.Negative
