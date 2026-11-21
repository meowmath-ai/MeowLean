import JSP000930PositiveMarkedBlockCompleteMap
import JSP000933RelativeTraceEnumeration

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B X : Type} [CompleteBooleanAlgebra B]

theorem restrictTotal_le_iff {S : Set X} (p : CohenTotal B X) (q : BlockTotal B S) :
    restrictTotal p S ≤ q ↔ p ≤ q.1 := by
  constructor
  · intro h
    have hp : p ≤ (restrictTotal p S).1 :=
      (cohen_total_le_iff _ _).mpr ⟨le_rfl,le_restrict p.trace S⟩
    exact hp.trans (show (restrictTotal p S).1 ≤ q.1 from h)
  · intro h
    have hr : restrictTotal p S ≤ restrictTotal q.1 S := restrictTotal_mono S h
    exact hr.trans (restrict_total_of_supported_le q)

theorem blockEmbed_image {S : Set X} (q : BlockTotal B S) :
    blockEmbed B S (imageCondition q) = imageCondition q.1 := by
  apply Heyting.Regular.coe_injective
  let F := cohenBlockProjection B S
  change F.lowerPull ((LowerSet.Iic q)ᶜᶜ) = (LowerSet.Iic q.1)ᶜᶜ
  rw [← F.lowerPull_compl,← F.lowerPull_compl]
  have h : F.lowerPull (LowerSet.Iic q) = LowerSet.Iic q.1 := by
    ext p
    exact restrictTotal_le_iff p q
  rw [h]

theorem markedBlock_pull_image {S : Set X}
    (q : TotalCondition (valuedBlock B S)) :
    (asMarkedBlock_dense S).pullIso (imageCondition q) =
      imageCondition ((asMarkedBlock S).symm q) := by
  apply Heyting.Regular.coe_injective
  let F := asMarkedBlock_dense (B := B) S
  change F.pullLower ((LowerSet.Iic q)ᶜᶜ) =
    (LowerSet.Iic ((asMarkedBlock S).symm q))ᶜᶜ
  rw [F.pullLower_compl,F.pullLower_compl]
  have h : F.pullLower (LowerSet.Iic q) = LowerSet.Iic ((asMarkedBlock S).symm q) := by
    ext p
    change (asMarkedBlock S) p ≤ q ↔ p ≤ (asMarkedBlock S).symm q
    exact (asMarkedBlock S).le_symm_apply.symm
  rw [h]

theorem markedBlockIntoFull_image {S : Set X}
    (q : TotalCondition (valuedBlock B S)) :
    (markedBlockIntoFull S).toFun (imageCondition q) =
      imageCondition ((asMarkedBlock S).symm q).1 := by
  change blockEmbed B S ((asMarkedBlock_dense S).pullIso (imageCondition q)) = _
  rw [markedBlock_pull_image,blockEmbed_image]

theorem markedBlock_rectangle {S : Set X} (q : BlockTrace S) (b : B) :
    (markedBlockIntoFull S).toFun (traceRectangle (valuedBlock B S) q b) =
      traceRectangle (valuedCohen B X) q.1 b := by
  by_cases hb : b = ⊥
  · subst b
    rw [traceRectangle_zero_r464,traceRectangle_zero_r464,(markedBlockIntoFull S).map_bot]
  · let q' : TotalCondition (valuedBlock B S) := ⟨b,q,hb,le_top⟩
    let p' : CohenTotal B X := ⟨b,q.1,hb,le_top⟩
    have hq : imageCondition q' = traceRectangle (valuedBlock B S) q b :=
      image_eq_base_meet_trace_r429 q'
    have hp : imageCondition p' = traceRectangle (valuedCohen B X) q.1 b :=
      image_eq_base_meet_trace_r429 p'
    rw [← hq,← hp,markedBlockIntoFull_image]
    rfl

end JSP000930.Positive.Cohen
