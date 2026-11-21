import JSP000930PositiveCanonicalNativeGrowthForcesLiteralEntire

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.SetLanguage JSP000933.OpenGraphForcing
  JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000930.SetLanguage

noncomputable def reservePointBits (c : OmegaOneIndex) : ComplexBits WetzelCohenBA :=
  realAxisBits (reserveRealBits c)

theorem reservePointBits_name (c : OmegaOneIndex) :
    (reservePointBits c).name = reservePoint c := rfl

theorem reservePointBits_cutOn (c : OmegaOneIndex) (p : WetzelCohenBA) :
    (reservePointBits c).CutOn p :=
  ⟨JSP000930.Positive.properCutOn_mono le_top (dyadicCut_is_proper (Sum.inr c : WetzelRow)),
    JSP000930.Positive.properCutOn_mono le_top (checkedRealBits_properCut 0)⟩

theorem canonical_valueCertificate_iff_reserveValue
    (E : LiteralTaylorEvalCorrespondence WetzelCohenBA)
    {n : ℕ} (v : DVec (V WetzelCohenBA) n) (c : OmegaOneIndex)
    (U : TaylorSlot → WetzelCohenBA) (W y : bSet WetzelCohenBA) (p : WetzelCohenBA)
    (hU : ∀ i,(complexCoeffBits U i).CutOn p)
    (hG : GrowthOn p (complexCoeffBits U)) :
    p ≤ valueCertificate v (reservePoint c) W (taylorCodeName U) y ↔
      p ≤ y =ᴮ reserveNativeValue c U := by
  let z := reservePointBits c
  let a := taylorCodeName U
  let u : DVec (V WetzelCohenBA) (n+4) := DVec.cons a (DVec.cons y (DVec.cons W (DVec.cons z.name v)))
  let A : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  have hA : bTerm u A = a :=
    bTerm_current_r181 (DVec.cons y (DVec.cons W (DVec.cons z.name v))) a
  have hE := canonical_native_data_forces_entire u A U p hA hU hG
  have hS : p ≤ bTruth u (sequence_f A) := by
    have h := hE
    unfold isEntireCode_f at h
    rw [bTruth_and_eq] at h
    exact h.trans inf_le_left
  obtain ⟨_,hc,_⟩ := sequenceBits_actual u A p hS
  have hG' := entire_growthOn u A p hE
  have hEq := canonical_sequence_bits_mask u A U p hA hS
  rw [hA] at hc hG' hEq
  have hEval := valueCertificate_iff_native_eval E v z W a y p
    (reservePointBits_cutOn c p) hE hc hG'
  rw [reservePointBits_name] at hEval
  have hSame : p ≤ (taylorLimitBits (sequenceBits a) z).name =ᴮ reserveNativeValue c U :=
    sameMaskedComplex_name (sameMaskedComplex_taylorLimit hEq (sameMaskedComplex_self p z))
  exact hEval.trans ⟨fun h => bv_trans h hSame,fun h => bv_trans h (bv_symm hSame)⟩

theorem reserveAnalyticLaw_of_literalEval
    (E : LiteralTaylorEvalCorrespondence WetzelCohenBA) : ReserveAnalyticLaw := by
  constructor
  · intro n v F p i c W x hF hM hAvail
    let U := decodeTaylorBits x
    obtain ⟨_,_,_,_,hCut,hG,_⟩ := literal_family_member_native_data v F U p hF hM
    let y := reserveNativeValue c U
    exact le_iSup_of_le y
      ((canonical_valueCertificate_iff_reserveValue E v c U W y p hCut hG).2 bv_refl)
  · intro n v F p c W y y' x x' hF hM hAvail hNe hVal hVal'
    let U := decodeTaylorBits x
    let D := decodeTaylorBits x'
    obtain ⟨_,_,_,_,hU,hGU,_⟩ :=
      literal_family_member_native_data v F U p hF (hM.trans inf_le_left)
    obtain ⟨_,_,_,_,hD,hGD,_⟩ :=
      literal_family_member_native_data v F D p hF (hM.trans inf_le_right)
    have hGood : p ≤ validDistinctTaylorPair U D :=
      (validDistinctTaylorPair_iff U D p).2
        ⟨(fun i b => by
          cases b
          · exact (hU i).1
          · exact (hU i).2), (fun i b => by
          cases b
          · exact (hD i).1
          · exact (hD i).2), hNe⟩
    have hSep := reserve_native_values_separate c x x' p hAvail hGood hGU hGD
    have hy := (canonical_valueCertificate_iff_reserveValue E v c U W y p hU hGU).1 hVal
    have hy' := (canonical_valueCertificate_iff_reserveValue E v c D W y' p hD hGD).1 hVal'
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hC : p ⊓ (y =ᴮ y') ≤ reserveNativeValue c U =ᴮ reserveNativeValue c D :=
      bv_trans (bv_symm (inf_le_left.trans hy))
        (bv_trans inf_le_right (inf_le_left.trans hy'))
    exact le_bot_iff.mpr (disjoint_compl_right.out _ hC (inf_le_left.trans hSep))

theorem wetzelCohen_forces_haymanAtAlephTwo_of_exact_eval
    (E : LiteralTaylorEvalCorrespondence WetzelCohenBA) :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] haymanAtAlephTwo_f :=
  wetzelCohen_forces_haymanAtAlephTwo_of_reserveAnalytic (reserveAnalyticLaw_of_literalEval E)

end JSP000930.Positive.Cohen
