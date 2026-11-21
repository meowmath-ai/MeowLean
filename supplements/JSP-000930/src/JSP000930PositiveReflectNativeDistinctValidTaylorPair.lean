import JSP000930PositiveMaskedProperCutTransfer

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

def validDistinctTaylorPair (u v : TaylorSlot → B) : B :=
  (⨅ n : ℕ,⨅ b : Bool,properCutValue (fun q => u (n,b,q))) ⊓
    ((⨅ n : ℕ,⨅ b : Bool,properCutValue (fun q => v (n,b,q))) ⊓
      (taylorCodeName u =ᴮ taylorCodeName v)ᶜ)

theorem validDistinctTaylorPair_iff (u v : TaylorSlot → B) (p : B) :
    p ≤ validDistinctTaylorPair u v ↔
    (∀ n b,ProperCutOn p (fun q => u (n,b,q))) ∧
    (∀ n b,ProperCutOn p (fun q => v (n,b,q))) ∧
    p ≤ (taylorCodeName u =ᴮ taylorCodeName v)ᶜ := by
  simp only [validDistinctTaylorPair,le_inf_iff,le_iInf_iff,le_properCutValue_iff]

theorem validDistinctTaylorPair_map (F : CompleteValueMap B C) (u v : TaylorSlot → B) :
    F.toFun (validDistinctTaylorPair u v) =
      validDistinctTaylorPair (fun j => F.toFun (u j)) (fun j => F.toFun (v j)) := by
  let N := coefficientsOfValueMap F
  have h : F.toFun (taylorCodeName u =ᴮ taylorCodeName v) =
      taylorCodeName (fun j => F.toFun (u j)) =ᴮ taylorCodeName (fun j => F.toFun (v j)) := by
    change N.map (taylorCodeName u =ᴮ taylorCodeName v) = _
    rw [← N.liftName_eq,liftName_taylorCode,liftName_taylorCode] <;> rfl
  simp only [validDistinctTaylorPair,F.map_inf,F.map_iInf,properCutValue_map,
    F.map_compl,h]

theorem le_image_validDistinctTaylorPair_of_same_mask
    (F : CompleteValueMap B C) (u v : TaylorSlot → B)
    (U V : TaylorSlot → C) (p : C)
    (hU : ∀ j,p ⊓ U j = p ⊓ F.toFun (u j))
    (hV : ∀ j,p ⊓ V j = p ⊓ F.toFun (v j))
    (h : p ≤ validDistinctTaylorPair U V) :
    p ≤ F.toFun (validDistinctTaylorPair u v) := by
  rw [validDistinctTaylorPair_map]
  obtain ⟨hCutU,hCutV,hNE⟩ := (validDistinctTaylorPair_iff U V p).1 h
  apply (validDistinctTaylorPair_iff _ _ p).2
  refine ⟨fun n b => properCutOn_of_same_mask (hCutU n b) (fun r => hU (n,b,r)),
    fun n b => properCutOn_of_same_mask (hCutV n b) (fun r => hV (n,b,r)),?_⟩
  have hEu := taylorCodeName_eq_of_mask hU
  have hEv := taylorCodeName_eq_of_mask hV
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  have he : p ⊓ (taylorCodeName (fun j => F.toFun (u j)) =ᴮ
      taylorCodeName (fun j => F.toFun (v j))) ≤ taylorCodeName U =ᴮ taylorCodeName V :=
    bv_trans (inf_le_left.trans hEu) (bv_trans inf_le_right (bv_symm (inf_le_left.trans hEv)))
  exact le_bot_iff.mpr
    (disjoint_compl_right.out _ he (inf_le_left.trans hNE))

end JSP000930.Positive
