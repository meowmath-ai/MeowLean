import JSP000933CompleteNameTransport
import JSP000933MarkedTraceRectangles
import JSP000933BooleanNamedCliqueStage
import JSP000933CompleteValueMap

open bSet
open scoped Flypitch

namespace JSP000933
namespace ForcingTransport

open MarkedForcing BooleanNames BooleanCompletion

variable {B N : Type} [NontrivialCompleteBooleanAlgebra B]

instance totalConditions_nonempty (Q : ValuedPoset B N) : Nonempty (TotalCondition Q) :=
  ⟨weakenToBase Q ⊤ top_ne_bot⟩

noncomputable def markedNameCoefficients (Q : ValuedPoset B N) :
    NameCoefficients B (TotalBA Q) where
  map := baseEmbed Q
  map_top := baseEmbed_top_r427 Q
  map_inf := baseEmbed_meets_r429 Q
  map_compl := baseEmbed_compl_r427 Q
  map_iSup := baseEmbed_joins_r427 Q

noncomputable def markedCompleteValueMap (Q : ValuedPoset B N) :
    CompleteValueMap B (TotalBA Q) where
  toFun := baseEmbed Q
  injective := fun _ _ h => le_antisymm
    ((baseEmbed_reflects_r428 Q).mp h.le) ((baseEmbed_reflects_r428 Q).mp h.ge)
  monotone := baseEmbed_mono_r427 Q
  map_bot := baseEmbed_bot_r427 Q
  map_top := baseEmbed_top_r427 Q
  map_compl := baseEmbed_compl_r427 Q
  map_inf := baseEmbed_meets_r429 Q
  map_iSup := baseEmbed_joins_r427 Q
  map_iInf := (markedNameCoefficients Q).map_iInf

theorem markedName_mem_iff (Q : ValuedPoset B N) (p : TotalCondition Q) (x y : bSet B) :
    BooleanCompletion.imageCondition p ≤
        ((markedNameCoefficients Q).liftName x ∈ᴮ (markedNameCoefficients Q).liftName y) ↔
      p.mask ≤ x ∈ᴮ y := by
  rw [(markedNameCoefficients Q).liftName_mem]
  exact baseEmbed_reflects_mask_r427 p _

theorem markedName_eq_iff (Q : ValuedPoset B N) (p : TotalCondition Q) (x y : bSet B) :
    BooleanCompletion.imageCondition p ≤
        ((markedNameCoefficients Q).liftName x =ᴮ (markedNameCoefficients Q).liftName y) ↔
      p.mask ≤ x =ᴮ y := by
  rw [(markedNameCoefficients Q).liftName_eq]
  exact baseEmbed_reflects_mask_r427 p _

theorem markedName_subset_iff (Q : ValuedPoset B N) (p : TotalCondition Q) (x y : bSet B) :
    BooleanCompletion.imageCondition p ≤
        ((markedNameCoefficients Q).liftName x ⊆ᴮ (markedNameCoefficients Q).liftName y) ↔
      p.mask ≤ x ⊆ᴮ y := by
  rw [(markedNameCoefficients Q).liftName_subset]
  exact baseEmbed_reflects_mask_r427 p _

end ForcingTransport
end JSP000933
