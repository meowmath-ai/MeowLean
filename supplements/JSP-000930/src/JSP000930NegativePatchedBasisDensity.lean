import JSP000930NegativePatchedPredenseCompleteMap
import JSP000933NativeBasePrefixCoherence

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B N I : Type} [CompleteBooleanAlgebra B] [Nonempty I]
    {Q : ValuedPoset B N} {m : B}
    {Nt : I → Type} {Qp : ∀ i,ValuedPoset B (Nt i)}

theorem LocalTraceInclusion.patchedDenseUnion
    (F : ∀ i, LocalTraceInclusion (Qp i) Q m)
    (hF : ∀ i, PreservesPredensity (F i).insideMap)
    (hD : ∀ q : MaskedCondition Q m,∃ (i : I) (d : MaskedCondition (Qp i) m),
      (F i).insideMap d ≤ q)
    (x : TotalBA (inertOutside Q m)) (hx : x ≠ ⊥) :
    ∃ (i : I) (v : TotalBA (inertOutside (Qp i) m)),
      ((F i).completePatchMap (hF i)).toFun v ≠ ⊥ ∧
      ((F i).completePatchMap (hF i)).toFun v ≤ x := by
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 x hx
  classical
  by_cases hin : q.mask ⊓ m ≠ ⊥
  · let r := intersectMask q m hin
    let r₀ := fromPatchCondition Q m r (show r.mask ≤ m from inf_le_right)
    obtain ⟨i,d,hd⟩ := hD r₀
    let d' := toPatchCondition (Qp i) m d
    refine ⟨i,imageCondition d',?_⟩
    rw [(F i).completePatchMap_image (hF i) d']
    refine ⟨imageCondition_ne_bot_r50 _,?_⟩
    apply (imageCondition_mono_r50 ?_).trans hq
    have h := (toPatch_order_iff Q m ((F i).insideMap d) r₀).mpr hd
    rw [(F i).inside_commutes] at h
    have h' : toPatchCondition Q m r₀ = r := toPatch_fromPatch _ _ _ _
    rw [h'] at h
    exact h.trans (intersectMask_le_r426 q m hin)
  · have hz : q.mask ⊓ m = ⊥ := by
      by_contra hn
      exact hin hn
    have hOut : q.mask ≤ mᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hz.le)
    let i : I := Classical.choice inferInstance
    let d := weakenToBase (inertOutside (Qp i) m) q.mask q.nonzero
    refine ⟨i,imageCondition d,?_⟩
    rw [(F i).completePatchMap_image (hF i) d]
    refine ⟨imageCondition_ne_bot_r50 _,(imageCondition_mono_r50 ?_).trans hq⟩
    exact ⟨le_rfl,hOut.trans le_sup_right⟩

theorem imageConditions_join (Q : ValuedPoset B N) (x : TotalBA Q) :
    (⨆ p : {p : TotalCondition Q // imageCondition p ≤ x},imageCondition p.val) = x := by
  apply le_antisymm (iSup_le fun p => p.property)
  apply JSP000933.ForcingTransport.le_of_image_tests
  intro p hp
  exact le_iSup (fun p : {p : TotalCondition Q // imageCondition p ≤ x} => imageCondition p.val) ⟨p,hp⟩

theorem LocalTraceInclusion.patchedCompleteMaps_comp
    {P M : Type} {Q₀ : ValuedPoset B P} {R : ValuedPoset B M}
    (G : LocalTraceInclusion Q₀ Q m) (hG : PreservesPredensity G.insideMap)
    (F : LocalTraceInclusion R Q m) (hF : PreservesPredensity F.insideMap)
    (E : LocalTraceInclusion Q₀ R m) (hE : PreservesPredensity E.insideMap)
    (h : ∀ t,F.label (E.label t) = G.label t)
    (x : TotalBA (inertOutside Q₀ m)) :
    (F.completePatchMap hF).toFun ((E.completePatchMap hE).toFun x) =
      (G.completePatchMap hG).toFun x := by
  rw [← imageConditions_join (inertOutside Q₀ m) x]
  simp only [CompleteValueMap.map_iSup,LocalTraceInclusion.completePatchMap_image]
  apply iSup_congr
  intro p
  have hp : F.patchMap (E.patchMap p.val) = G.patchMap p.val := by
    unfold LocalTraceInclusion.patchMap
    simp only [h]
  exact congrArg imageCondition hp

end JSP000930.Negative
