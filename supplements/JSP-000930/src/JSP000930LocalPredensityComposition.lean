import JSP000930IndependentActiveRowRestriction
import JSP000930NegativePreparedMaskedLimit

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {P Q R : Type} [Preorder P] [Preorder Q] [Preorder R]

theorem preservesPredensity_comp930 (f : P→Q) (g : Q→R)
    (hgMono : Monotone g) (hf : PreservesPredensity f) (hg : PreservesPredensity g) :
    PreservesPredensity (g ∘ f) := by
  intro D hD r
  let E : Set Q := {q | ∃ d∈D,q≤f d}
  have hE : DenseConditionSet E := by
    intro q
    obtain ⟨d,hd,s,hsq,hsd⟩ := hf D hD q
    exact ⟨s,hsq,d,hd,hsd⟩
  obtain ⟨q,hq,s,hsr,hsq⟩ := hg E hE r
  obtain ⟨d,hd,hqd⟩ := hq
  exact ⟨d,hd,s,hsr,hsq.trans (hgMono hqd)⟩

variable {B X Y Z : Type} [CompleteBooleanAlgebra B]
variable {A : ValuedPoset B X} {C : ValuedPoset B Y} {D : ValuedPoset B Z} {m : B}

theorem LocalTraceInclusion.insideMap_mono930 (F : LocalTraceInclusion A C m) :
    Monotone F.insideMap := by
  intro p q h
  change p.val.mask ≤ q.val.mask ∧ p.val.mask ≤ C.refines (F.label p.val.trace) (F.label q.val.trace)
  have ht := le_inf p.property h.2
  rw [← F.refines] at ht
  exact ⟨h.1,ht.trans inf_le_right⟩

def LocalTraceInclusion.comp930 (F : LocalTraceInclusion A C m) (G : LocalTraceInclusion C D m) :
    LocalTraceInclusion A D m where
  label := G.label ∘ F.label
  valid t := (G.valid _).trans (F.valid t)
  refines t u := (G.refines _ _).trans (F.refines t u)
  reflectCommon t u := (G.reflectCommon _ _).trans (F.reflectCommon t u)

theorem LocalTraceInclusion.insideMap_ext930 (F G : LocalTraceInclusion A C m)
    (h : ∀ t,F.label t = G.label t) (p : MaskedCondition A m) :
    F.insideMap p = G.insideMap p := by
  apply Subtype.ext
  exact totalCondition_eq_of_data _ _ rfl (h p.val.trace)

theorem LocalTraceInclusion.insideMap_comp930 (F : LocalTraceInclusion A C m)
    (G : LocalTraceInclusion C D m) (p : MaskedCondition A m) :
    (F.comp930 G).insideMap p = G.insideMap (F.insideMap p) := by
  apply Subtype.ext
  exact totalCondition_eq_of_data _ _ rfl rfl

theorem LocalTraceInclusion.predense_comp930 (F : LocalTraceInclusion A C m)
    (G : LocalTraceInclusion C D m) (hF : PreservesPredensity F.insideMap)
    (hG : PreservesPredensity G.insideMap) : PreservesPredensity (F.comp930 G).insideMap := by
  have h : (F.comp930 G).insideMap = G.insideMap ∘ F.insideMap :=
    funext (F.insideMap_comp930 G)
  rw [h]
  exact preservesPredensity_comp930 _ _ G.insideMap_mono930 hF hG

end JSP000930.Negative
