import JSP000930NegativePatchedBasisDensity
import JSP000930PositiveMixedEnumerationInjection

open Cardinal

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.PreparedModel
  JSP000930.Positive JSP000933.RelativeOCA

variable {N I : Type} [LinearOrder I] [Nonempty I]
  {Nt : I → Type} {Q : ValuedPoset PreparedBA N}
  {Qp : ∀ i,ValuedPoset PreparedBA (Nt i)} {m : PreparedBA}

structure MaskedContinuousTower (Q : ValuedPoset PreparedBA N)
    (Qp : ∀ i,ValuedPoset PreparedBA (Nt i)) (m : PreparedBA) where
  into : ∀ i,LocalTraceInclusion (Qp i) Q m
  shift : ∀ i j,i ≤ j → LocalTraceInclusion (Qp i) (Qp j) m
  into_predense : ∀ i,PreservesPredensity (into i).insideMap
  shift_predense : ∀ i j (h : i ≤ j),PreservesPredensity (shift i j h).insideMap
  coherent : ∀ i j (h : i ≤ j) t,(into j).label ((shift i j h).label t) = (into i).label t
  final_dense : ∀ q : MaskedCondition Q m,∃ (i : I) (d : MaskedCondition (Qp i) m),
    (into i).insideMap d ≤ q
  earlier_dense : ∀ j,CheckedGroundLimit j → ∀ q : MaskedCondition (Qp j) m,
    ∃ (i : I) (h : i < j) (d : MaskedCondition (Qp i) m),
      (shift i j h.le).insideMap d ≤ q

noncomputable def MaskedContinuousTower.patched (C : MaskedContinuousTower Q Qp m) :
    CompleteStageTower (totalBaseMap (inertOutside Q m))
      (fun i => TotalBA (inertOutside (Qp i) m)) where
  stage i := (C.into i).completePatchMap (C.into_predense i)
  base i := totalBaseMap (inertOutside (Qp i) m)
  shift i j h := (C.shift i j h).completePatchMap (C.shift_predense i j h)
  base_coherent i b := (C.into i).completePatchMap_base (C.into_predense i) b
  shift_coherent i j h a := (C.into i).patchedCompleteMaps_comp (C.into_predense i)
    (C.into j) (C.into_predense j) (C.shift i j h) (C.shift_predense i j h) (C.coherent i j h) a
  final_dense x hx := LocalTraceInclusion.patchedDenseUnion
    C.into C.into_predense C.final_dense x hx

theorem MaskedContinuousTower.patched_continuous (C : MaskedContinuousTower Q Qp m) :
    ContinuousStageTower C.patched := by
  intro j hj x hx
  let J := {i : I // i < j}
  letI : Nonempty J := by
    obtain ⟨i,hi⟩ := hj.1
    exact ⟨⟨i,hi⟩⟩
  let F (i : J) := C.shift i.val j i.property.le
  have hF (i : J) : PreservesPredensity (F i).insideMap :=
    C.shift_predense i.val j i.property.le
  have hD (q : MaskedCondition (Qp j) m) :
      ∃ (i : J) (d : MaskedCondition (Qp i.val) m),(F i).insideMap d ≤ q := by
    obtain ⟨i,hi,d,hd⟩ := C.earlier_dense j hj q
    exact ⟨⟨i,hi⟩,d,hd⟩
  obtain ⟨i,v,hv,hvx⟩ := LocalTraceInclusion.patchedDenseUnion F hF hD x hx
  refine ⟨i.val,i.property,v,?_,hvx⟩
  intro he
  let E := (F i).completePatchMap (hF i)
  exact hv ((congrArg E.toFun he).trans E.map_bot)

theorem relativeCCCOn_of_prepared_masked_small_limit [WellFoundedLT I]
    (C : MaskedContinuousTower Q Qp m) (hI : Cardinal.mk I ≤ 𝔠)
    (hCCC : ∀ i,RelativeCCCOn (Qp i) m) :
    RelativeCCCOn Q m := by
  apply (inertOutside_relativeCCC_iff Q m).mp
  exact relativeCCC_of_prepared_continuous_small_limit
    (inertOutside Q m) (fun i => inertOutside (Qp i) m)
    C.patched C.patched_continuous hI (fun _ _ => rfl)
    (fun i => (inertOutside_relativeCCC_iff (Qp i) m).mpr (hCCC i))

theorem RelativeCCCOn.of_global (Q : ValuedPoset PreparedBA N)
    (m : PreparedBA) (h : ForcesRelativeCCC Q) : RelativeCCCOn Q m := by
  intro W hW hSep
  rw [h W hW hSep,inf_bot_eq]

theorem relativeCCC_of_covering_masked_small_limits
    {K : Type} (m : K → PreparedBA) (hM : (⨆ k,m k) = ⊤)
    {J : K → Type} [∀ k,LinearOrder (J k)] [∀ k,WellFoundedLT (J k)]
    [∀ k,Nonempty (J k)] {Ns : ∀ k,J k → Type}
    (Qs : ∀ k (i : J k),ValuedPoset PreparedBA (Ns k i))
    (C : ∀ k,MaskedContinuousTower Q (Qs k) (m k))
    (hI : ∀ k,Cardinal.mk (J k) ≤ 𝔠)
    (hCCC : ∀ k i,RelativeCCCOn (Qs k i) (m k)) :
    ForcesRelativeCCC Q :=
  relativeCCC_glue Q m hM (fun k => relativeCCCOn_of_prepared_masked_small_limit
    (C k) (hI k) (hCCC k))

theorem relativeCCCOn_of_prepared_masked_checkedKappa_limit
    {Ts : GroundContinuumSuccIndex → Type}
    {Q0 : ∀ i,ValuedPoset PreparedBA (Ts i)}
    (C : MaskedContinuousTower Q Q0 m)
    (hCCC : ∀ i,RelativeCCCOn (Q0 i) m) :
    RelativeCCCOn Q m := by
  apply (inertOutside_relativeCCC_iff Q m).mp
  exact relativeCCC_of_prepared_checkedKappa_limit
    (inertOutside Q m) (fun i => inertOutside (Q0 i) m)
    (by
      letI : Nonempty GroundContinuumSuccIndex := ⟨continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos⟩
      exact C.patched) (fun _ _ => rfl)
    (fun i => (inertOutside_relativeCCC_iff (Q0 i) m).mpr (hCCC i))

end JSP000930.Negative
