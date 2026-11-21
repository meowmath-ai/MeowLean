import JSP000930PositiveMarkedCohen
import JSP000930PositiveReserveKernels

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B X : Type} [CompleteBooleanAlgebra B]

def Prescribes (p : Trace X) (x : X) (b : Bool) : Prop :=
  x ∈ p.1.dom ∧ p.1.bit x = b

noncomputable def bitSlice (B : Type) [CompleteBooleanAlgebra B] (x : X) (b : Bool) :
    CohenBA B X :=
  ⨆ p : {p : TotalCondition (valuedCohen B X) // Prescribes p.trace x b},
    imageCondition p.val

theorem image_le_bitSlice (p : TotalCondition (valuedCohen B X))
    (x : X) (b : Bool) (h : Prescribes p.trace x b) :
    imageCondition p ≤ bitSlice B x b := le_iSup (fun q : {q : TotalCondition (valuedCohen B X) // Prescribes q.trace x b} =>
      imageCondition q.val) ⟨p,h⟩

theorem disagree_bits_not_compatible
    (p q : TotalCondition (valuedCohen B X)) (x : X) {a b : Bool}
    (hp : Prescribes p.trace x a) (hq : Prescribes q.trace x b) (hab : a ≠ b) :
    ¬ Compatible p q := by
  rintro ⟨r,hrp,hrq⟩
  have hp' : Extends r.trace.1 p.trace.1 := ((cohen_total_le_iff r p).mp hrp).2
  have hq' : Extends r.trace.1 q.trace.1 := ((cohen_total_le_iff r q).mp hrq).2
  exact hab (((hp'.2 x hp.1).trans hp.2).symm.trans ((hq'.2 x hq.1).trans hq.2))

theorem bitSlice_disjoint (x : X) {a b : Bool} (hab : a ≠ b) :
    Disjoint (bitSlice B x a) (bitSlice B x b) := by
  apply disjoint_iff_inf_le.mpr
  simp only [bitSlice,iSup_inf_iSup]
  apply iSup_le
  rintro ⟨p,q⟩
  apply disjoint_iff_inf_le.mp
  by_contra hg
  exact disagree_bits_not_compatible p.val q.val x p.property q.property hab
    ((compatible_iff_not_disjoint_r50 p.val q.val).mpr hg)

theorem bitSlice_cover (x : X) :
    bitSlice B x false ⊔ bitSlice B x true = ⊤ := by
  apply compl_injective
  rw [compl_top]
  apply value_eq_bot_of_dense_avoidance
  intro p hp
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 p hp
  classical
  by_cases hx : x ∈ q.trace.1.dom
  · refine ⟨imageCondition q,imageCondition_ne_bot_r50 q,hq,?_⟩
    have hq' : imageCondition q ≤ bitSlice B x false ⊔ bitSlice B x true := by
      cases h : q.trace.1.bit x
      · exact (image_le_bitSlice q x false ⟨hx,h⟩).trans le_sup_left
      · exact (image_le_bitSlice q x true ⟨hx,h⟩).trans le_sup_right
    exact le_bot_iff.mp (disjoint_iff_inf_le.mp (disjoint_compl_right.mono_left hq'))
  · obtain ⟨t,ht,hm,he⟩ := trace_decide_fresh q.trace x false hx
    let r : TotalCondition (valuedCohen B X) := ⟨q.mask,t,q.nonzero,le_top⟩
    have hr : r ≤ q := (cohen_total_le_iff _ _).mpr ⟨le_rfl,ht⟩
    refine ⟨imageCondition r,imageCondition_ne_bot_r50 r,
      (imageCondition_mono_r50 hr).trans hq,?_⟩
    have hr' : imageCondition r ≤ bitSlice B x false ⊔ bitSlice B x true :=
      (image_le_bitSlice r x false ⟨hm,he⟩).trans le_sup_left
    exact le_bot_iff.mp (disjoint_iff_inf_le.mp (disjoint_compl_right.mono_left hr'))

theorem bitSlice_false_eq_compl_true (x : X) :
    bitSlice B x false = (bitSlice B x true)ᶜ := by
  have hC : IsCompl (bitSlice B x false) (bitSlice B x true) :=
    ⟨bitSlice_disjoint (B := B) x (by decide),
      codisjoint_iff.mpr (bitSlice_cover (B := B) x)⟩
  exact hC.eq_compl

end JSP000930.Positive.Cohen
