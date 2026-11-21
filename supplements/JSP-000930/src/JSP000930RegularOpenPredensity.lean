import JSP000930SymbolicMarkedPrefixMap

namespace JSP000930.Negative

open JSP000933.BooleanCompletion

universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

def DenseConditionSet (D : Set P) : Prop := ∀ p : P,∃ q : P,q ≤ p ∧ q ∈ D

def PreservesPredensity (f : P → Q) : Prop :=
  ∀ D : Set P,DenseConditionSet D → ∀ q : Q,∃ d : P,d ∈ D ∧ Compatible q (f d)

noncomputable def basisImage (f : P → Q) (U : RO P) : RO Q :=
  ⨆ p : {p : P // p ∈ (U : LowerSet P)},imageCondition (f p.1)

theorem basisImage_mono (f : P → Q) : Monotone (basisImage f) := by
  intro U V h
  apply iSup_le
  intro p
  exact le_iSup (fun q : {q : P // q ∈ (V : LowerSet P)} => imageCondition (f q.1))
    ⟨p.1,h p.2⟩

theorem basisImage_of_member (f : P → Q) (U : RO P) {p : P}
    (hp : p ∈ (U : LowerSet P)) : imageCondition (f p) ≤ basisImage f U :=
  le_iSup (fun q : {q : P // q ∈ (U : LowerSet P)} => imageCondition (f q.1)) ⟨p,hp⟩

theorem predense_basis_top (f : P → Q) (hf : PreservesPredensity f)
    (D : Set P) (hD : DenseConditionSet D) :
    (⨆ d : D,imageCondition (f d.1)) = (⊤ : RO Q) := by
  apply top_unique
  let U : RO Q := ⨆ d : D,imageCondition (f d.1)
  change ⊤ ≤ U
  by_contra h
  have hU : Uᶜ ≠ ⊥ := fun he => h ((compl_eq_bot.mp he).ge)
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 Uᶜ hU
  obtain ⟨d,hd,r,hRQ,hRD⟩ := hf D hD q
  have hR : imageCondition r ≤ U :=
    (imageCondition_mono_r50 hRD).trans (le_iSup (fun x : D => imageCondition (f x.val)) ⟨d,hd⟩)
  exact imageCondition_ne_bot_r50 r (disjoint_compl_right.out _ hR
    ((imageCondition_mono_r50 hRQ).trans hq))

theorem dense_regular_side (U : RO P) :
    DenseConditionSet {p | p ∈ (U : LowerSet P) ∨ p ∈ ((Uᶜ : RO P) : LowerSet P)} := by
  intro p
  classical
  by_cases h : ∃ q ≤ p,q ∈ (U : LowerSet P)
  · obtain ⟨q,hq,hU⟩ := h
    exact ⟨q,hq,Or.inl hU⟩
  · refine ⟨p,le_rfl,Or.inr ?_⟩
    change p ∈ ((U : LowerSet P)ᶜ : LowerSet P)
    apply (mem_pseudoCompl_r50 _ p).mpr
    exact fun q hqp hq => h ⟨q,hqp,hq⟩

theorem basisImage_join_compl (f : P → Q) (hf : PreservesPredensity f) (U : RO P) :
    basisImage f U ⊔ basisImage f Uᶜ = ⊤ := by
  apply top_unique
  let D : Set P := {p | p ∈ (U : LowerSet P) ∨ p ∈ ((Uᶜ : RO P) : LowerSet P)}
  rw [← predense_basis_top f hf D (dense_regular_side U)]
  apply iSup_le
  intro d
  rcases d.2 with hd | hd
  · exact (basisImage_of_member f U hd).trans le_sup_left
  · exact (basisImage_of_member f Uᶜ hd).trans le_sup_right

theorem basisImage_disjoint_compl (f : P → Q)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q) (U : RO P) :
    Disjoint (basisImage f U) (basisImage f Uᶜ) := by
  apply disjoint_iff_inf_le.mpr
  unfold basisImage
  rw [iSup_inf_eq]
  apply iSup_le
  intro p
  rw [inf_iSup_eq]
  apply iSup_le
  intro q
  apply disjoint_iff_inf_le.mp
  by_contra h
  obtain ⟨r,hrp,hrq⟩ := hReflect ((compatible_iff_not_disjoint_r50 _ _).mpr h)
  have hrU : r ∈ (U : LowerSet P) := (U : LowerSet P).lower hrp p.2
  have hq : q.1 ∈ ((U : LowerSet P)ᶜ : LowerSet P) := q.2
  exact (mem_pseudoCompl_r50 _ q.1).mp hq r hrq hrU

theorem basisImage_compl (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q) (U : RO P) :
    basisImage f Uᶜ = (basisImage f U)ᶜ := by
  have hc : IsCompl (basisImage f U) (basisImage f Uᶜ) :=
    ⟨basisImage_disjoint_compl f hReflect U,
      codisjoint_iff_le_sup.mpr (basisImage_join_compl f hf U).ge⟩
  exact hc.compl_eq.symm

end JSP000930.Negative
