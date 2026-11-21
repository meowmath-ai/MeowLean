import JSP000930CompleteMapFromNativeIso
import JSP000930MarkedForcingPairOps
import JSP000933StaticSuccessor

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport
open JSP000933.FiniteSupport

variable {B N M : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def pairFirst (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition (valuedPair P Q)) : TotalCondition P :=
  ⟨p.mask,p.trace.1,p.nonzero,p.valid.trans inf_le_left⟩

noncomputable def pairToIterated (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition (valuedPair P Q)) :
    TotalCondition (changeValuedBase (markedCompleteValueMap P) Q) :=
  ⟨imageCondition (pairFirst P Q p),p.trace.2,imageCondition_ne_bot_r50 _,
   (baseEmbed_reflects_mask_r427 _ _).mpr (p.valid.trans inf_le_right)⟩

theorem pairToIterated_mono (P : ValuedPoset B N) (Q : ValuedPoset B M) :
    Monotone (pairToIterated P Q) := by
  intro p q h
  have hP : pairFirst P Q p ≤ pairFirst P Q q := ⟨h.1,h.2.trans inf_le_left⟩
  refine ⟨imageCondition_mono_r50 hP,?_⟩
  exact (baseEmbed_reflects_mask_r427 _ _).mpr (h.2.trans inf_le_right)

theorem pairToIterated_dense (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (r : TotalCondition (changeValuedBase (markedCompleteValueMap P) Q)) :
    ∃ s : TotalCondition (valuedPair P Q),pairToIterated P Q s ≤ r := by
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 r.mask r.nonzero
  have hq : p.mask ≤ Q.valid r.trace := (baseEmbed_reflects_mask_r427 _ _).mp (hp.trans r.valid)
  let s : TotalCondition (valuedPair P Q) := ⟨p.mask,(p.trace,r.trace),p.nonzero,le_inf p.valid hq⟩
  have h : pairFirst P Q s = p := by cases p; rfl
  refine ⟨s,?_⟩
  change imageCondition (pairFirst P Q s) ≤ r.mask ∧
    imageCondition (pairFirst P Q s) ≤ (markedCompleteValueMap P).toFun (Q.refines r.trace r.trace)
  rw [h]
  exact ⟨hp,(baseEmbed_reflects_mask_r427 _ _).mpr (hq.trans (Q.refl _))⟩

theorem pairToIterated_reflects_compatible (P : ValuedPoset B N) (Q : ValuedPoset B M)
    {p q : TotalCondition (valuedPair P Q)}
    (h : Compatible (pairToIterated P Q p) (pairToIterated P Q q)) :
    Compatible p q := by
  obtain ⟨c,hcp,hcq⟩ := h
  obtain ⟨r,hrp,hrq,hrC⟩ := exists_common_prefix_below_r86 (pairFirst P Q p) (pairFirst P Q q)
    c.nonzero hcp.1 hcq.1
  have hR : r.mask ≤ Q.valid c.trace :=
    (baseEmbed_reflects_mask_r427 r _).mp (hrC.trans c.valid)
  let t : TotalCondition (valuedPair P Q) := ⟨r.mask,(r.trace,c.trace),r.nonzero,le_inf r.valid hR⟩
  have hTp : r.mask ≤ Q.refines c.trace p.trace.2 :=
    (baseEmbed_reflects_mask_r427 r _).mp (hrC.trans hcp.2)
  have hTq : r.mask ≤ Q.refines c.trace q.trace.2 :=
    (baseEmbed_reflects_mask_r427 r _).mp (hrC.trans hcq.2)
  exact ⟨t,⟨hrp.1,le_inf hrp.2 hTp⟩,⟨hrq.1,le_inf hrq.2 hTq⟩⟩

noncomputable def pairIteratedDenseMap (P : ValuedPoset B N) (Q : ValuedPoset B M) :
    DenseForcingMap (TotalCondition (valuedPair P Q))
      (TotalCondition (changeValuedBase (markedCompleteValueMap P) Q)) :=
  ⟨pairToIterated P Q,pairToIterated_mono P Q,pairToIterated_dense P Q,
    pairToIterated_reflects_compatible P Q⟩

theorem pairIteratedDenseMap_base (P : ValuedPoset B N) (Q : ValuedPoset B M) (b : B) :
    (pairIteratedDenseMap P Q).pullIso
      (baseEmbed (changeValuedBase (markedCompleteValueMap P) Q) (baseEmbed P b)) =
        baseEmbed (valuedPair P Q) b := by
  let D := pairIteratedDenseMap P Q
  let W := changeValuedBase (markedCompleteValueMap P) Q
  have ht (p : TotalCondition (valuedPair P Q)) :
      imageCondition p ≤ D.pullIso (baseEmbed W (baseEmbed P b)) ↔
      imageCondition p ≤ baseEmbed (valuedPair P Q) b := by
    rw [image_le_iff_member]
    change D.map p ∈ (baseEmbed W (baseEmbed P b) : LowerSet _) ↔ _
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427,baseEmbed_reflects_mask_r427]
    change imageCondition (pairFirst P Q p) ≤ baseEmbed P b ↔ p.mask ≤ b
    exact baseEmbed_reflects_mask_r427 _ _
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
    (le_of_image_tests (fun p => (ht p).mpr))

end JSP000930.Negative
