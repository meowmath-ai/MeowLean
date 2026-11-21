import JSP000930RegularOpenPredensityJoins

namespace JSP000930.Negative

open JSP000933.BooleanCompletion

universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem basisImage_bot (f : P → Q) : basisImage f ⊥ = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro p
  have hp : p.1 ∈ (⊥ : LowerSet P) := p.2
  simp at hp

theorem basisImage_top (f : P → Q) (hf : PreservesPredensity f) :
    basisImage f ⊤ = ⊤ := by
  simpa only [compl_top,basisImage_bot,sup_bot_eq] using basisImage_join_compl f hf ⊤

theorem basisImage_iInf (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q)
    {I : Type u} (U : I → RO P) :
    basisImage f (⨅ i,U i) = ⨅ i,basisImage f (U i) := by
  have hDeMorgan : (⨅ i,U i) = (⨆ i,(U i)ᶜ)ᶜ := by
    rw [compl_iSup]
    simp only [compl_compl]
  rw [hDeMorgan,basisImage_compl f hf hReflect,basisImage_iSup f hf hReflect,compl_iSup]
  exact iInf_congr (fun i => by rw [basisImage_compl f hf hReflect,compl_compl])

private theorem map_inf_from_iInf {A C : Type u} [CompleteLattice A] [CompleteLattice C]
    (g : A → C) (hg : ∀ X : ULift.{u} Bool → A, g (⨅ i, X i) = ⨅ i, g (X i))
    (a b : A) : g (a ⊓ b) = g a ⊓ g b := by
  let X : ULift.{u} Bool → A := fun i => if i.down then a else b
  have hX : (⨅ i, X i) = a ⊓ b := by
    apply le_antisymm
    · exact le_inf (iInf_le X ⟨true⟩) (iInf_le X ⟨false⟩)
    · apply le_iInf
      rintro ⟨i⟩
      cases i
      · exact inf_le_right
      · exact inf_le_left
  have hG : (⨅ i, g (X i)) = g a ⊓ g b := by
    apply le_antisymm
    · exact le_inf (iInf_le (g ∘ X) ⟨true⟩) (iInf_le (g ∘ X) ⟨false⟩)
    · apply le_iInf
      rintro ⟨i⟩
      cases i
      · exact inf_le_right
      · exact inf_le_left
  rw [← hX, hg X, hG]

theorem basisImage_inf (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q) (U V : RO P) :
    basisImage f (U ⊓ V) = basisImage f U ⊓ basisImage f V :=
  map_inf_from_iInf (basisImage f) (basisImage_iInf f hf hReflect) U V

theorem basisImage_reflect_bot (f : P → Q) {U : RO P} (h : basisImage f U = ⊥) : U = ⊥ := by
  by_contra hU
  obtain ⟨p,hp⟩ := nonbot_exists_member_r50 hU
  exact imageCondition_ne_bot_r50 (f p) (le_bot_iff.mp
    ((basisImage_of_member f U hp).trans h.le))

theorem basisImage_reflect_le (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q) {U V : RO P}
    (h : basisImage f U ≤ basisImage f V) : U ≤ V := by
  have h0 : basisImage f (U ⊓ Vᶜ) = ⊥ := by
    rw [basisImage_inf f hf hReflect,basisImage_compl f hf hReflect]
    exact le_bot_iff.mp (disjoint_iff_inf_le.mp (disjoint_compl_right_iff.mpr h))
  exact disjoint_compl_right_iff.mp
    (disjoint_iff_inf_le.mpr (basisImage_reflect_bot f h0).le)

noncomputable def completeMapFromPredensity (f : P → Q) (hf : PreservesPredensity f)
    (hReflect : ∀ {p q},Compatible (f p) (f q) → Compatible p q) :
    CompleteValueMap (RO P) (RO Q) where
  toFun := basisImage f
  injective := fun _ _ h => le_antisymm (basisImage_reflect_le f hf hReflect h.le)
    (basisImage_reflect_le f hf hReflect h.ge)
  monotone := basisImage_mono f
  map_bot := basisImage_bot f
  map_top := basisImage_top f hf
  map_compl := basisImage_compl f hf hReflect
  map_inf := basisImage_inf f hf hReflect
  map_iSup := basisImage_iSup f hf hReflect
  map_iInf := basisImage_iInf f hf hReflect

end JSP000930.Negative
