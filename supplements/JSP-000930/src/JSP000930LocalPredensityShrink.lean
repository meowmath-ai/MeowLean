import JSP000930LocalPredensityComposition

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B X Y : Type} [CompleteBooleanAlgebra B]
variable {A : ValuedPoset B X} {C : ValuedPoset B Y} {m s : B}

def LocalTraceInclusion.shrink930 (F : LocalTraceInclusion A C m) (hs : s ≤ m) :
    LocalTraceInclusion A C s where
  label := F.label
  valid t := by
    have h := congrArg (fun x : B => s ⊓ x) (F.valid t)
    simpa only [← inf_assoc,inf_eq_left.mpr hs] using h
  refines t u := by
    have h := congrArg (fun x : B => s ⊓ x) (F.refines t u)
    simpa only [← inf_assoc,inf_eq_left.mpr hs] using h
  reflectCommon t u := by
    have h := inf_le_inf (le_refl s) (F.reflectCommon t u)
    simpa only [← inf_assoc,inf_eq_left.mpr hs] using h

theorem LocalTraceInclusion.predense_shrink930 (F : LocalTraceInclusion A C m)
    (hF : PreservesPredensity F.insideMap) (hs : s ≤ m) :
    PreservesPredensity (F.shrink930 hs).insideMap := by
  classical
  intro D hD q
  let E : Set (MaskedCondition A m) := {p |
    Disjoint p.val.mask s ∨ ∃ hp : p.val.mask ≤ s, (⟨p.val,hp⟩ : MaskedCondition A s) ∈ D}
  have hE : DenseConditionSet E := by
    intro p
    by_cases hp : p.val.mask ⊓ s = ⊥
    · exact ⟨p,le_rfl,Or.inl (disjoint_iff_inf_le.mpr hp.le)⟩
    · let p₀ : MaskedCondition A s := ⟨intersectMask p.val s hp,inf_le_right⟩
      obtain ⟨d,hd,hD'⟩ := hD p₀
      let d' : MaskedCondition A m := ⟨d.val,d.property.trans hs⟩
      have hdp : d.val ≤ p₀.val := hd
      exact ⟨d',hdp.trans (intersectMask_le_r426 p.val s hp),Or.inr ⟨d.property,hD'⟩⟩
  let q' : MaskedCondition C m := ⟨q.val,q.property.trans hs⟩
  obtain ⟨d,hd,w,hwq,hwd⟩ := hF E hE q'
  have hw : w.val.mask ≤ s := hwq.1.trans q.property
  refine Or.elim hd ?_ ?_
  · intro hd'
    have he : w.val.mask ≤ d.val.mask ⊓ s := le_inf hwd.1 hw
    exact False.elim (w.val.nonzero (le_bot_iff.mp (he.trans (disjoint_iff_inf_le.mp hd'))))
  · rintro ⟨hd',hD'⟩
    let d' : MaskedCondition A s := ⟨d.val,hd'⟩
    let w' : MaskedCondition C s := ⟨w.val,hw⟩
    refine ⟨d',hD',w',hwq,?_⟩
    have he : ((F.shrink930 hs).insideMap d').val = (F.insideMap d).val :=
      totalCondition_eq_of_data _ _ rfl rfl
    change w.val ≤ ((F.shrink930 hs).insideMap d').val
    rw [he]
    exact hwd

end JSP000930.Negative
