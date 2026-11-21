import JSP000930CertifiedMarkedPoset

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport
open CertifiedStageLabel

variable {B N : Type} [CompleteBooleanAlgebra B]

def certifiedConditionHead (Q : ValuedPoset B N) (p : TotalCondition (certifiedQ Q)) :
    TotalCondition Q :=
  ⟨p.mask,p.trace.head Q,p.nonzero,p.valid.trans (admits_le_head Q p.trace)⟩

theorem certifiedConditionHead_mono (Q : ValuedPoset B N) :
    Monotone (certifiedConditionHead Q) := by
  intro p q hpq
  have hp := (certifiedTotal_le_iff Q p q).mp hpq
  refine ⟨hp.1,?_⟩
  change p.mask ≤ Q.refines (p.trace.head Q) (q.trace.head Q)
  cases h : q.trace with
  | weak =>
    exact (p.valid.trans (admits_le_head Q p.trace)).trans (Q.weaker _)
  | list n l =>
    have hmem : n ∈ q.trace.stored := by rw [h]; exact List.mem_cons_self
    have hIn : n ∈ p.trace.stored := hp.2.1 n hmem
    exact p.valid.trans (admits_le_stored Q p.trace n hIn)

theorem certifiedConditionHead_dense (Q : ValuedPoset B N) (p : TotalCondition Q) :
    ∃ q : TotalCondition (certifiedQ Q),certifiedConditionHead Q q ≤ p := by
  let q : TotalCondition (certifiedQ Q) := ⟨p.mask,.list p.trace [] [],p.nonzero,
    by change p.mask ≤ admits Q (.list p.trace [] []); rw [admits_singleton]; exact p.valid⟩
  have h : certifiedConditionHead Q q = p := by cases p; rfl
  exact ⟨q,h.le⟩

theorem certifiedConditionHead_reflects_compatible (Q : ValuedPoset B N)
    {p q : TotalCondition (certifiedQ Q)}
    (h : Compatible (certifiedConditionHead Q p) (certifiedConditionHead Q q)) :
    Compatible p q := by
  obtain ⟨r,hrP,hrQ⟩ := h
  let t : CertifiedStageLabel N := mergeWithHead r.trace p.trace q.trace
  have hT : r.mask ≤ admits Q t :=
    admits_fresh_head Q r.trace p.trace q.trace r.mask hrP.2 hrQ.2
      (hrP.1.trans p.valid) (hrQ.1.trans q.valid)
  let w : TotalCondition (certifiedQ Q) := ⟨r.mask,t,r.nonzero,hT⟩
  exact ⟨w,(certifiedTotal_le_iff Q w p).mpr ⟨hrP.1,mergeWithHead_left _ _ _⟩,
    (certifiedTotal_le_iff Q w q).mpr ⟨hrQ.1,mergeWithHead_right _ _ _⟩⟩

noncomputable def certifiedHeadDenseMap (Q : ValuedPoset B N) :
    DenseForcingMap (TotalCondition (certifiedQ Q)) (TotalCondition Q) :=
  ⟨certifiedConditionHead Q,certifiedConditionHead_mono Q,certifiedConditionHead_dense Q,
    certifiedConditionHead_reflects_compatible Q⟩

theorem certifiedHeadDenseMap_base (Q : ValuedPoset B N) (b : B) :
    (certifiedHeadDenseMap Q).pullIso (baseEmbed Q b) = baseEmbed (certifiedQ Q) b := by
  let D := certifiedHeadDenseMap Q
  change D.pullIso (baseEmbed Q b) = baseEmbed (certifiedQ Q) b
  have ht (p : TotalCondition (certifiedQ Q)) :
      imageCondition p ≤ D.pullIso (baseEmbed Q b) ↔ imageCondition p ≤ baseEmbed (certifiedQ Q) b := by
    rw [image_le_iff_member]
    change D.map p ∈ (baseEmbed Q b : LowerSet (TotalCondition Q)) ↔ _
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427,baseEmbed_reflects_mask_r427] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
    (le_of_image_tests (fun p => (ht p).mpr))

end JSP000930.Negative
