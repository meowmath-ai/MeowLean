import JSP000930NegativeLocalTraceInclusion
import JSP000930RegularOpenBasicCoherence

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B N M : Type} [CompleteBooleanAlgebra B]
  {Q : ValuedPoset B N} {R : ValuedPoset B M} {m : B}

theorem LocalTraceInclusion.patch_predense (F : LocalTraceInclusion Q R m)
    (hF : PreservesPredensity F.insideMap) : PreservesPredensity F.patchMap := by
  intro D hD q
  classical
  by_cases hin : q.mask ⊓ m ≠ ⊥
  · let r := intersectMask q m hin
    let r₀ := fromPatchCondition R m r (show r.mask ≤ m from inf_le_right)
    let D₀ : Set (MaskedCondition Q m) := {p | toPatchCondition Q m p ∈ D}
    have hD₀ : DenseConditionSet D₀ := by
      intro p
      obtain ⟨d,hdp,hdD⟩ := hD (toPatchCondition Q m p)
      have hdm : d.mask ≤ m := hdp.1.trans p.property
      let d₀ := fromPatchCondition Q m d hdm
      have hEq : toPatchCondition Q m d₀ = d := toPatch_fromPatch Q m d hdm
      refine ⟨d₀,(toPatch_order_iff Q m _ _).mp ?_,?_⟩
      · rw [hEq]; exact hdp
      · change toPatchCondition Q m d₀ ∈ D
        rw [hEq]; exact hdD
    obtain ⟨d,hd,⟨w,hwr,hwd⟩⟩ := hF D₀ hD₀ r₀
    refine ⟨toPatchCondition Q m d,hd,⟨toPatchCondition R m w,?_,?_⟩⟩
    · have h := (toPatch_order_iff R m w r₀).mpr hwr
      change toPatchCondition R m w ≤ toPatchCondition R m (fromPatchCondition R m r _) at h
      rw [toPatch_fromPatch] at h
      exact h.trans (intersectMask_le_r426 q m hin)
    · have h := (toPatch_order_iff R m w (F.insideMap d)).mpr hwd
      rw [F.inside_commutes] at h
      exact h
  · have hz : q.mask ⊓ m = ⊥ := by
      by_contra hn
      exact hin hn
    have hOut : q.mask ≤ mᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hz.le)
    let p := weakenToBase (inertOutside Q m) q.mask q.nonzero
    obtain ⟨d,hdp,hdD⟩ := hD p
    have hdq : d.mask ≤ q.mask := hdp.1
    have hhc : d.mask ≤ commonRefinementValue (inertOutside R m) q.trace (F.label d.trace) := by
      rw [inertOutside_common]
      exact (hdq.trans hOut).trans le_sup_right
    refine ⟨d,hdD,(totalCompatible_iff_r426 q (F.patchMap d)).mpr ?_⟩
    change (q.mask ⊓ d.mask) ⊓ commonRefinementValue (inertOutside R m) q.trace (F.label d.trace) ≠ ⊥
    rw [inf_eq_right.mpr hdq,inf_eq_left.mpr hhc]
    exact d.nonzero

noncomputable def LocalTraceInclusion.completePatchMap
    (F : LocalTraceInclusion Q R m) (hF : PreservesPredensity F.insideMap) :
    CompleteValueMap (TotalBA (inertOutside Q m)) (TotalBA (inertOutside R m)) :=
  completeMapFromPredensity F.patchMap (F.patch_predense hF) (fun {p q} h => F.patch_reflect_compat h)

theorem LocalTraceInclusion.completePatchMap_image
    (F : LocalTraceInclusion Q R m) (hF : PreservesPredensity F.insideMap)
    (p : TotalCondition (inertOutside Q m)) :
    (F.completePatchMap hF).toFun (imageCondition p) = imageCondition (F.patchMap p) :=
  completeMapFromPredensity_image F.patchMap
    (fun p q hp => (F.patchOrder_iff p q).mpr hp)
    (F.patch_predense hF) (fun {p q} h => F.patch_reflect_compat h) p

theorem LocalTraceInclusion.completePatchMap_base
    (F : LocalTraceInclusion Q R m) (hF : PreservesPredensity F.insideMap) (b : B) :
    (F.completePatchMap hF).toFun (baseEmbed (inertOutside Q m) b) =
      baseEmbed (inertOutside R m) b := by
  let E := F.completePatchMap hF
  have hLE (a : B) : E.toFun (baseEmbed (inertOutside Q m) a) ≤
      baseEmbed (inertOutside R m) a := by
    unfold baseEmbed
    rw [E.map_iSup]
    exact iSup_le fun p => (F.completePatchMap_image hF p.val).trans_le
      (image_le_baseEmbed_r427 (F.patchMap p.val) a p.property)
  apply le_antisymm (hLE b)
  have hh := compl_le_compl (hLE bᶜ)
  rw [baseEmbed_compl_r427,baseEmbed_compl_r427,E.map_compl,compl_compl,compl_compl] at hh
  exact hh

end JSP000930.Negative
