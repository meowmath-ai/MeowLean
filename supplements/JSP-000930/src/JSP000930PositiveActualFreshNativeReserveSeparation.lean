import JSP000930PositiveNativeTaylorLimitRespectsMask

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.CantorCodes JSP000933.PreparedModel JSP000933.OpenGraphForcing
  JSP000930.BooleanAnalysis

theorem reserve_native_values_separate
    (c : OmegaOneIndex) (x z : ℕ → WetzelCohenBA) (p : WetzelCohenBA)
    (hAvail : p ≤ availableAtReserve x c ⊓ availableAtReserve z c)
    (hGood : p ≤ validDistinctTaylorPair (decodeTaylorBits x) (decodeTaylorBits z))
    (hGX : GrowthOn p (complexCoeffBits (decodeTaylorBits x)))
    (hGZ : GrowthOn p (complexCoeffBits (decodeTaylorBits z))) :
    p ≤ (reserveNativeValue c (decodeTaylorBits x) =ᴮ
      reserveNativeValue c (decodeTaylorBits z))ᶜ := by
  apply reduce_fresh_pair_to_earlier_taylor c x z p _ hAvail hGood
  intro u v _ _ _ _ _ _
  let F := reserveEarlierEmbed c
  let d := p ⊓ (realEqValue x (fun n => F.toFun (u n)) ⊓
    realEqValue z (fun n => F.toFun (v n)))
  let U := decodeTaylorBits u
  let V := decodeTaylorBits v
  let A := fun j => F.toFun (U j)
  let D := fun j => F.toFun (V j)
  have hu : d ≤ realEqValue x (fun n => F.toFun (u n)) := inf_le_right.trans inf_le_left
  have hv : d ≤ realEqValue z (fun n => F.toFun (v n)) := inf_le_right.trans inf_le_right
  have hU (j : TaylorSlot) : d ⊓ decodeTaylorBits x j = d ⊓ A j := by
    letI := taylorSlotEncodable
    exact (le_realEqValue_iff_r126 d _ _).mp hu (Encodable.encode j)
  have hV (j : TaylorSlot) : d ⊓ decodeTaylorBits z j = d ⊓ D j := by
    letI := taylorSlotEncodable
    exact (le_realEqValue_iff_r126 d _ _).mp hv (Encodable.encode j)
  have hD := valid_growth_pair_earlier_values F U V (decodeTaylorBits x)
    (decodeTaylorBits z) d hU hV (inf_le_left.trans hGood)
    (hGX.mono inf_le_left) (hGZ.mono inf_le_left)
  have hNe : d ≤ (reserveNativeValue c A =ᴮ reserveNativeValue c D)ᶜ :=
    hD.trans (reserve_separates_earlier_native_taylor c U V _ le_rfl)
  let P := realAxisBits (reserveRealBits c)
  have hEqU : d ≤ reserveNativeValue c (decodeTaylorBits x) =ᴮ reserveNativeValue c A :=
    sameMaskedComplex_name (sameMaskedComplex_taylorLimit
      (fun n => ⟨fun q => hU (n,false,q),fun q => hU (n,true,q)⟩)
      (sameMaskedComplex_self d P))
  have hEqV : d ≤ reserveNativeValue c (decodeTaylorBits z) =ᴮ reserveNativeValue c D :=
    sameMaskedComplex_name (sameMaskedComplex_taylorLimit
      (fun n => ⟨fun q => hV (n,false,q),fun q => hV (n,true,q)⟩)
      (sameMaskedComplex_self d P))
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  have hC : d ⊓ (reserveNativeValue c (decodeTaylorBits x) =ᴮ
      reserveNativeValue c (decodeTaylorBits z)) ≤ reserveNativeValue c A =ᴮ reserveNativeValue c D :=
    bv_trans (bv_symm (inf_le_left.trans hEqU))
      (bv_trans inf_le_right (inf_le_left.trans hEqV))
  exact le_bot_iff.mpr (disjoint_compl_right.out _ hC (inf_le_left.trans hNe))

end JSP000930.Positive.Cohen
