import JSP000930PositiveReflectNativeDistinctValidTaylorPair
import JSP000930PositiveExactPointwiseCapWiring

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.CantorCodes
  JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.ForcingTransport

abbrev ReserveEarlierBA (c : OmegaOneIndex) :=
  TotalBA (valuedBlock PreparedBA (reservePrefix c))

noncomputable abbrev reserveEarlierEmbed (c : OmegaOneIndex) :
    CompleteValueMap (ReserveEarlierBA c) WetzelCohenBA :=
  markedBlockIntoFull (B := PreparedBA) (reservePrefix c)

theorem reduce_fresh_pair_to_earlier_taylor (c : OmegaOneIndex)
    (x z : ℕ → WetzelCohenBA) (p goal : WetzelCohenBA)
    (hAvail : p ≤ availableAtReserve x c ⊓ availableAtReserve z c)
    (hGood : p ≤ validDistinctTaylorPair (decodeTaylorBits x) (decodeTaylorBits z))
    (hEarlier : ∀ u v : ℕ → ReserveEarlierBA c,
      let F := reserveEarlierEmbed c
      let d := p ⊓ (realEqValue x (fun n => F.toFun (u n)) ⊓
        realEqValue z (fun n => F.toFun (v n)))
      let m := validDistinctTaylorPair (decodeTaylorBits u) (decodeTaylorBits v)
      d ≤ F.toFun m →
      d ≤ (taylorCodeName (decodeTaylorBits x) =ᴮ
        (coefficientsOfValueMap F).liftName (taylorCodeName (decodeTaylorBits u))) →
      d ≤ (taylorCodeName (decodeTaylorBits z) =ᴮ
        (coefficientsOfValueMap F).liftName (taylorCodeName (decodeTaylorBits v))) →
      d ≤ goal) :
    p ≤ goal := by
  let F := reserveEarlierEmbed c
  apply (le_inf le_rfl hAvail).trans
  change (p ⊓ ((⨆ u : ℕ → ReserveEarlierBA c,realEqValue x (fun n => F.toFun (u n))) ⊓
    (⨆ v : ℕ → ReserveEarlierBA c,realEqValue z (fun n => F.toFun (v n))))) ≤ goal
  rw [iSup_inf_iSup]
  rw [inf_iSup_eq]
  apply iSup_le
  rintro ⟨u,v⟩
  let d := p ⊓ (realEqValue x (fun n => F.toFun (u n)) ⊓
    realEqValue z (fun n => F.toFun (v n)))
  have hu : d ≤ realEqValue x (fun n => F.toFun (u n)) := inf_le_right.trans inf_le_left
  have hv : d ≤ realEqValue z (fun n => F.toFun (v n)) := inf_le_right.trans inf_le_right
  have hU (j : TaylorSlot) : d ⊓ decodeTaylorBits x j =
      d ⊓ F.toFun (decodeTaylorBits u j) := by
    letI := taylorSlotEncodable
    exact (le_realEqValue_iff_r126 d _ _).mp hu (Encodable.encode j)
  have hV (j : TaylorSlot) : d ⊓ decodeTaylorBits z j =
      d ⊓ F.toFun (decodeTaylorBits v j) := by
    letI := taylorSlotEncodable
    exact (le_realEqValue_iff_r126 d _ _).mp hv (Encodable.encode j)
  refine hEarlier u v
    (le_image_validDistinctTaylorPair_of_same_mask F _ _ _ _ d hU hV (inf_le_left.trans hGood)) ?_ ?_
  · rw [liftName_taylorCode]
    exact taylorCodeName_eq_of_mask hU
  · rw [liftName_taylorCode]
    exact taylorCodeName_eq_of_mask hV

end JSP000930.Positive.Cohen
