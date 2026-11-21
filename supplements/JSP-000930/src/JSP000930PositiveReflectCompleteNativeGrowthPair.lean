import JSP000930PositiveNativeGrowthMaskedCongruence
import JSP000930PositiveLocalizedFreshPairActualPrefix

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

theorem le_map_growth_of_same_mask (F : CompleteValueMap B C)
    (u : TaylorSlot → B) (U : TaylorSlot → C) (p : C)
    (hEq : ∀ j,p ⊓ U j = p ⊓ F.toFun (u j))
    (hGrowth : GrowthOn p (complexCoeffBits U)) :
    p ≤ F.toFun (growthValue (complexCoeffBits u)) := by
  rw [growthValue_map]
  have hMask := masked_growthValue_congr (p := p) (U := complexCoeffBits U)
    (V := fun n => mapComplexBits F (complexCoeffBits u n))
    (fun n q => hEq (n,false,q)) (fun n q => hEq (n,true,q))
  exact (le_inf le_rfl ((growthValue_le_iff _ _).2 hGrowth)).trans
    (hMask.le.trans inf_le_right)

theorem valid_growth_pair_earlier_values
    (F : CompleteValueMap B C)
    (u v : TaylorSlot → B) (U V : TaylorSlot → C) (p : C)
    (hEqU : ∀ j,p ⊓ U j = p ⊓ F.toFun (u j))
    (hEqV : ∀ j,p ⊓ V j = p ⊓ F.toFun (v j))
    (hValid : p ≤ validDistinctTaylorPair U V)
    (hGrowthU : GrowthOn p (complexCoeffBits U))
    (hGrowthV : GrowthOn p (complexCoeffBits V)) :
    p ≤ F.toFun (validDistinctTaylorPair u v ⊓
      (growthValue (complexCoeffBits u) ⊓ growthValue (complexCoeffBits v))) := by
  simp only [F.map_inf]
  exact le_inf (le_image_validDistinctTaylorPair_of_same_mask F u v U V p hEqU hEqV hValid)
    (le_inf (le_map_growth_of_same_mask F u U p hEqU hGrowthU)
      (le_map_growth_of_same_mask F v V p hEqV hGrowthV))

theorem earlier_values_admissible
    (u v : TaylorSlot → B)
    (p : B) (hp : p ≤ validDistinctTaylorPair u v ⊓
      (growthValue (complexCoeffBits u) ⊓ growthValue (complexCoeffBits v))) :
    (∀ n,(complexCoeffBits u n).CutOn p) ∧
      (∀ n,(complexCoeffBits v n).CutOn p) ∧
      GrowthOn p (complexCoeffBits u) ∧ GrowthOn p (complexCoeffBits v) := by
  obtain ⟨hU,hV,_⟩ := (validDistinctTaylorPair_iff u v p).1 (hp.trans inf_le_left)
  refine ⟨fun n => ⟨hU n false,hU n true⟩,fun n => ⟨hV n false,hV n true⟩,?_ ,?_⟩
  · exact (growthValue_le_iff _ _).1 (hp.trans (inf_le_right.trans inf_le_left))
  · exact (growthValue_le_iff _ _).1 (hp.trans (inf_le_right.trans inf_le_right))

end JSP000930.Positive
