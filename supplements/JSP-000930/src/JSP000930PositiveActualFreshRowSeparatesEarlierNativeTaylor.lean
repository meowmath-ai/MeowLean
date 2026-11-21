import JSP000930PositiveRationalCertificatesCompleteTransport

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.PreparedModel
  JSP000933.OpenGraphForcing JSP000930.Positive.Dyadic JSP000930.BooleanAnalysis

noncomputable def reserveRealBits (c : OmegaOneIndex) : RatPresentation → WetzelCohenBA :=
  dyadicCutBits (B := PreparedBA) (Sum.inr c : WetzelRow)

noncomputable def reserveNativeValue (c : OmegaOneIndex) (U : TaylorSlot → WetzelCohenBA) :
    bSet WetzelCohenBA :=
  (taylorLimitBits (complexCoeffBits U) (realAxisBits (reserveRealBits c))).name

theorem reserve_separates_earlier_native_taylor
    (c : OmegaOneIndex) (U V : TaylorSlot → ReserveEarlierBA c)
    (m : ReserveEarlierBA c)
    (hm : m ≤ validDistinctTaylorPair U V ⊓
      (growthValue (complexCoeffBits U) ⊓ growthValue (complexCoeffBits V))) :
    (reserveEarlierEmbed c).toFun m ≤
      (reserveNativeValue c (fun j => (reserveEarlierEmbed c).toFun (U j)) =ᴮ
        reserveNativeValue c (fun j => (reserveEarlierEmbed c).toFun (V j)))ᶜ := by
  let S := reservePrefix c
  let F := reserveEarlierEmbed c
  let E := (asMarkedBlock_dense (B := PreparedBA) S).pullIso
  let i : WetzelRow := Sum.inr c
  let A := fun j => F.toFun (U j)
  let D := fun j => F.toFun (V j)
  let goal := (reserveNativeValue c A =ᴮ reserveNativeValue c D)ᶜ
  have hF : F.toFun m ≤ validDistinctTaylorPair A D ⊓
      (growthValue (complexCoeffBits A) ⊓ growthValue (complexCoeffBits D)) := by
    have h := F.monotone hm
    simpa only [F.map_inf,validDistinctTaylorPair_map,growthValue_map,
      mapComplexBits_coeff,A,D] using h
  obtain ⟨hA,hD,hGA,hGD⟩ := earlier_values_admissible A D (F.toFun m) hF
  let cert (ab : ℚ × ℚ) := E (earlierCertificateUnion U V m ab)
  have hDense (w : List Bool) :
      E m ≤ ⨆ ab : {ab : ℚ × ℚ // ProperSubinterval w ab},cert ab.val := by
    have h := E.monotone (earlierCertificateUnion_dense U V m w hm)
    simpa only [cert,OrderIso.map_iSup] using h
  change blockEmbed PreparedBA S (E m) ≤ goal
  apply fresh_row_from_rational_interval_certificates S i (reserveRow_fresh c) (E m) cert hDense
  intro w ab hw
  change wordValue PreparedBA i w ⊓ F.toFun (earlierCertificateUnion U V m ab) ≤ goal
  rw [earlierCertificateUnion,F.map_iSup,inf_iSup_eq]
  apply iSup_le
  intro K
  let p := wordValue PreparedBA i w ⊓ F.toFun (m ⊓ K.value U V)
  have hp : p ≤ F.toFun m := inf_le_right.trans (F.monotone inf_le_left)
  have hK : p ≤ K.value A D := by
    rw [← K.value_map F]
    exact inf_le_right.trans (F.monotone inf_le_right)
  obtain ⟨lo,hlo⟩ := ratPresentation_value_surjective ab.1
  obtain ⟨hi,hhi⟩ := ratPresentation_value_surjective ab.2
  have hz : p ≤ reserveRealBits c lo ⊓ (reserveRealBits c hi)ᶜ :=
    le_inf (inf_le_left.trans (dyadicCutBit_below_left i w lo (by rw [hlo]; exact hw.1)))
      (inf_le_left.trans (dyadicCutBit_above_right i w hi (by rw [hhi]; exact hw.2.le)))
  have hZ : ProperCutOn p (reserveRealBits c) :=
    JSP000930.Positive.properCutOn_mono le_top (dyadicCut_is_proper i)
  exact certificate_forces_native_separation K A D (reserveRealBits c) p
    (fun n => ⟨JSP000930.Positive.properCutOn_mono hp (hA n).1,
      JSP000930.Positive.properCutOn_mono hp (hA n).2⟩)
    (fun n => ⟨JSP000930.Positive.properCutOn_mono hp (hD n).1,
      JSP000930.Positive.properCutOn_mono hp (hD n).2⟩)
    hZ (hGA.mono hp) (hGD.mono hp) lo hi hlo hhi hz hK

end JSP000930.Positive.Cohen
