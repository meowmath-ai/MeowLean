import JSP000930PositiveBlockRelativeCCC
import JSP000933CompleteValueMap

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport

variable {B X : Type} [CompleteBooleanAlgebra B]

theorem markedBlock_le_iff {S : Set X}
    (p q : TotalCondition (valuedBlock B S)) :
    p ≤ q ↔ p.mask ≤ q.mask ∧ p.trace ≤ q.trace :=
  ⟨fun h => ⟨h.1,(blockRefines_iff S p.nonzero p.trace q.trace).mp h.2⟩,
    fun h => ⟨h.1,(blockRefines_iff S p.nonzero p.trace q.trace).mpr h.2⟩⟩

noncomputable def asMarkedBlock (S : Set X) :
    BlockTotal B S ≃o TotalCondition (valuedBlock B S) where
  toFun p := ⟨p.1.mask,⟨p.1.trace,p.2⟩,p.1.nonzero,le_top⟩
  invFun p := ⟨⟨p.mask,p.trace.1,p.nonzero,le_top⟩,p.trace.2⟩
  left_inv p := by
    rcases p with ⟨⟨m,t,hm,hv⟩,hs⟩
    rfl
  right_inv p := by
    rcases p with ⟨m,⟨t,hs⟩,hm,hv⟩
    rfl
  map_rel_iff' := by
    intro p q
    rw [markedBlock_le_iff]
    exact (cohen_total_le_iff p.1 q.1).symm

noncomputable def asMarkedBlock_dense (S : Set X) :
    DenseForcingMap (BlockTotal B S) (TotalCondition (valuedBlock B S)) where
  map := asMarkedBlock S
  monotone := (asMarkedBlock S).monotone
  dense q := ⟨(asMarkedBlock S).symm q,by simp⟩
  reflect_compatible := by
    rintro p q ⟨r,hrp,hrq⟩
    exact ⟨(asMarkedBlock S).symm r,
      by simpa using (asMarkedBlock S).symm.monotone hrp,
      by simpa using (asMarkedBlock S).symm.monotone hrq⟩

noncomputable def markedBlockIntoFull (S : Set X) :
    CompleteValueMap (TotalBA (valuedBlock B S)) (CohenBA B X) where
  toFun a := blockEmbed B S ((asMarkedBlock_dense S).pullIso a)
  injective := (blockEmbed_injective S).comp (asMarkedBlock_dense S).pullIso.injective
  monotone := ((cohenBlockProjection B S).pull_mono).comp
    (asMarkedBlock_dense S).pullIso.monotone
  map_bot := by
    have h := (cohenBlockProjection B S).pull_compl (⊤ : CohenBlockBA B S)
    change blockEmbed B S ((asMarkedBlock_dense S).pullIso ⊥) = ⊥
    rw [OrderIso.map_bot]
    change (cohenBlockProjection B S).pull ⊥ = ⊥
    simpa only [compl_top,(cohenBlockProjection B S).pull_top] using h
  map_top := by simp only [OrderIso.map_top,blockEmbed_top]
  map_compl a := by
    have h := (asMarkedBlock_dense S).pull_compl a
    change blockEmbed B S ((asMarkedBlock_dense S).pull aᶜ) =
      (blockEmbed B S ((asMarkedBlock_dense S).pull a))ᶜ
    rw [h,blockEmbed_compl]
  map_inf a b := by rw [OrderIso.map_inf,blockEmbed_inf]
  map_iSup U := by rw [OrderIso.map_iSup,blockEmbed_general_iSup]
  map_iInf U := by
    rw [OrderIso.map_iInf]
    exact (cohenBlockProjection B S).pull_iInf _

end JSP000930.Positive.Cohen
