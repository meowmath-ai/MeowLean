import JSP000933BooleanBasicSupport
import JSP000933ProperStageCardinality

open scoped Cardinal

namespace JSP000933
namespace BooleanCompletion

open OpenGraphForcing FiniteSupport

variable {P : Type} [Preorder P]

theorem exists_omegaOneEnumeration_of_bits_r99 (hCCC : BooleanCCC (RO P))
    (hSize : Cardinal.mk P ≤ ℵ₁) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ f : OmegaOneIndex → ℕ → RO P, Function.Surjective f := by
  classical
  have hPoints : Cardinal.mk P ≤ Cardinal.mk RealCode := by
    rwa [mk_realCode_r61,CH]
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hPoints
  obtain ⟨encode,hEncode⟩ := exists_binaryCode_for_realBits_r98 hCCC e e.injective
  have hBits : Cardinal.mk (ℕ → RO P) ≤ Cardinal.mk OmegaOneIndex := by
    rw [mk_OmegaOneIndex_r61,← CH,← mk_realCode_r61]
    exact Cardinal.mk_le_of_injective hEncode
  obtain ⟨j⟩ := (Cardinal.le_def _ _).mp hBits
  let f (i : OmegaOneIndex) : ℕ → RO P :=
    if h : ∃ r : ℕ → RO P, j r = i then Classical.choose h else fun _ => ⊥
  refine ⟨f,fun r => ⟨j r,?_⟩⟩
  have h : ∃ y : ℕ → RO P, j y = j r := ⟨r,rfl⟩
  apply j.injective
  simpa only [f,dite_eq_left h] using Classical.choose_spec h

theorem exists_omegaOneEnumeration_properStage_r99
    (a : OmegaTwoIndex) (V : PrefixValidator a ((Finset OmegaOneIndex)ᵒᵈ))
    (hCCC : BooleanCCC (RO (GoodPrefix V))) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ f : OmegaOneIndex → ℕ → RO (GoodPrefix V), Function.Surjective f :=
  exists_omegaOneEnumeration_of_bits_r99 hCCC
    (mk_GoodPrefix_le_alephOne_r97 (V := V) (mk_omegaTwo_properPrefix_le_alephOne_r97 a)
      mk_groundCliqueLabels_r97.le) CH

end BooleanCompletion
end JSP000933
