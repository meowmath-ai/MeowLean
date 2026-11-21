import JSP000930NegativeTwoStepAdmissibility

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport

variable {B N M : Type} [CompleteBooleanAlgebra B]
  (Q : ValuedPoset B N) (S : ValuedPoset (TotalBA Q) M)

def augmentedFirst (p : TotalCondition (augmentedQ Q S)) : TotalCondition Q :=
  ⟨p.mask,p.trace.1,p.nonzero,p.valid.trans inf_le_left⟩

theorem augmentedFirst_image (p : TotalCondition (augmentedQ Q S)) :
    imageCondition (augmentedFirst Q S p) = traceRectangle Q p.trace.1 p.mask :=
  image_eq_base_meet_trace_r429 _

noncomputable def augmentedConditionMap (p : TotalCondition (augmentedQ Q S)) :
    TotalCondition S :=
  ⟨imageCondition (augmentedFirst Q S p),p.trace.2,imageCondition_ne_bot_r50 _,
    (augmentedFirst_image Q S p).trans_le ((le_augmentedAdmissible_iff _ _ _ _).mp
      (p.valid.trans inf_le_right))⟩

theorem augmentedConditionMap_mono : Monotone (augmentedConditionMap Q S) := by
  intro p q hp
  have h₁ : augmentedFirst Q S p ≤ augmentedFirst Q S q :=
    ⟨hp.1,hp.2.trans (inf_le_right.trans inf_le_left)⟩
  exact ⟨imageCondition_mono_r50 h₁,(augmentedFirst_image Q S p).trans_le
    ((le_augmentedAdmissible_iff _ _ _ _).mp (hp.2.trans (inf_le_right.trans inf_le_right)))⟩

noncomputable def augmentedPairOf (p : TotalCondition Q) (t : M)
    (h : imageCondition p ≤ S.valid t) : TotalCondition (augmentedQ Q S) :=
  ⟨p.mask,(p.trace,t),p.nonzero,le_inf p.valid
    ((le_augmentedAdmissible_iff _ _ _ _).mpr ((image_eq_base_meet_trace_r429 p).symm.trans_le h))⟩

theorem augmentedPairOf_first (p : TotalCondition Q) (t : M)
    (h : imageCondition p ≤ S.valid t) :
    augmentedFirst Q S (augmentedPairOf Q S p t h) = p := by cases p; rfl

theorem augmentedConditionMap_dense (r : TotalCondition S) :
    ∃ p,augmentedConditionMap Q S p ≤ r := by
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 r.mask r.nonzero
  let p := augmentedPairOf Q S q r.trace (hq.trans r.valid)
  refine ⟨p,?_⟩
  change imageCondition (augmentedFirst Q S p) ≤ r.mask ∧
    imageCondition (augmentedFirst Q S p) ≤ S.refines r.trace r.trace
  rw [augmentedPairOf_first]
  exact ⟨hq,(hq.trans r.valid).trans (S.refl _)⟩

private theorem twoBasic_common_below (p q : TotalCondition Q) (x : TotalBA Q) (hx : x ≠ ⊥)
    (hp : x ≤ imageCondition p) (hq : x ≤ imageCondition q) :
    ∃ r : TotalCondition Q,r ≤ p ∧ r ≤ q ∧ imageCondition r ≤ x := by
  have hm : imageCondition p ⊓ x ≠ ⊥ := by rw [inf_eq_right.mpr hp]; exact hx
  obtain ⟨a,hap,ha⟩ := exists_stronger_below_of_meet_r51 p x hm
  have hc : Compatible a q := by
    apply (compatible_iff_not_disjoint_r50 a q).mpr
    intro hd
    exact imageCondition_ne_bot_r50 a (hd.out _ le_rfl (ha.trans hq))
  obtain ⟨w,hwa,hwq⟩ := hc
  exact ⟨w,hwa.trans hap,hwq,(imageCondition_mono_r50 hwa).trans ha⟩

theorem augmentedConditionMap_reflects_compatible
    {p q : TotalCondition (augmentedQ Q S)} :
    Compatible (augmentedConditionMap Q S p) (augmentedConditionMap Q S q) →
    Compatible p q := by
  rintro ⟨r,hrp,hrq⟩
  obtain ⟨w,hwp,hwq,hw⟩ := twoBasic_common_below Q (augmentedFirst Q S p)
    (augmentedFirst Q S q) r.mask r.nonzero hrp.1 hrq.1
  let z := augmentedPairOf Q S w r.trace (hw.trans r.valid)
  have hW : traceRectangle Q w.trace w.mask ≤ r.mask :=
    (image_eq_base_meet_trace_r429 w).symm.trans_le hw
  refine ⟨z,⟨hwp.1,?_⟩,⟨hwq.1,?_⟩⟩
  · exact le_inf (le_inf z.valid (hwp.1.trans p.valid))
      (le_inf hwp.2 ((le_augmentedAdmissible_iff _ _ _ _).mpr (hW.trans hrp.2)))
  · exact le_inf (le_inf z.valid (hwq.1.trans q.valid))
      (le_inf hwq.2 ((le_augmentedAdmissible_iff _ _ _ _).mpr (hW.trans hrq.2)))

noncomputable def augmentedDenseMap :
    DenseForcingMap (TotalCondition (augmentedQ Q S)) (TotalCondition S) where
  map := augmentedConditionMap Q S
  monotone := augmentedConditionMap_mono Q S
  dense := augmentedConditionMap_dense Q S
  reflect_compatible := augmentedConditionMap_reflects_compatible Q S

end JSP000930.Negative
