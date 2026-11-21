import JSP000930PositiveExplicitCutValidityNaturality
import JSP000930AnalyticRadiusTrace

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.PositiveForcing
  JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

theorem checkedRealBits_map (F : CompleteValueMap B C) (x : ℝ) (q : RatPresentation) :
    F.toFun (checkedRealBits (B := B) x q) = checkedRealBits (B := C) x q := by
  by_cases h : (q.value : ℝ) < x <;>
    simp [checkedRealBits,crispTruth,h,F.map_bot,F.map_top]

theorem addCutBits_map (F : CompleteValueMap B C) (u v : RatPresentation → B)
    (q : RatPresentation) :
    F.toFun (addCutBits u v q) =
      addCutBits (fun r => F.toFun (u r)) (fun r => F.toFun (v r)) q := by
  simp only [addCutBits,F.map_iSup,F.map_inf,completeMap_proof_iSup]

theorem mulCutBits_map (F : CompleteValueMap B C) (u v : RatPresentation → B)
    (q : RatPresentation) :
    F.toFun (mulCutBits u v q) =
      mulCutBits (fun r => F.toFun (u r)) (fun r => F.toFun (v r)) q := by
  simp only [mulCutBits,intervalBits,F.map_iSup,F.map_inf,F.map_compl,completeMap_proof_iSup]

def mapComplexBits (F : CompleteValueMap B C) (u : ComplexBits B) : ComplexBits C :=
  ⟨fun q => F.toFun (u.re q),fun q => F.toFun (u.im q)⟩

theorem radiusBudgetBits_map (F : CompleteValueMap B C) (a : ComplexBits B)
    (R K n : ℕ) :
    F.toFun (radiusBudgetBits a R K n) =
      radiusBudgetBits (mapComplexBits F a) R K n := by
  let E := coefficientsOfValueMap F
  unfold radiusBudgetBits
  change E.map (_ ⊆ᴮ _) = _
  rw [← E.liftName_subset,liftName_cut,liftName_cut]
  simp only [E,coefficientsOfValueMap,ComplexBits.normSq,mapComplexBits,mulCutBits_map,
    addCutBits_map,checkedRealBits_map]

noncomputable def growthValue (A : ℕ → ComplexBits B) : B :=
  ⨅ R : ℕ,⨅ (_ : 1 ≤ R),⨆ K : ℕ,⨅ n : ℕ,radiusBudgetBits (A n) R K n

theorem growthValue_le_iff (a : ℕ → ComplexBits B) (p : B) :
    p ≤ growthValue a ↔ GrowthOn p a := by
  simp only [growthValue,GrowthOn,le_iInf_iff]

theorem growthValue_map (F : CompleteValueMap B C) (a : ℕ → ComplexBits B) :
    F.toFun (growthValue a) = growthValue (fun n => mapComplexBits F (a n)) := by
  simp only [growthValue,F.map_iInf,completeMap_proof_iInf,F.map_iSup,radiusBudgetBits_map]

def complexCoeffBits (u : TaylorSlot → B) (n : ℕ) : ComplexBits B :=
  ⟨fun q => u (n,false,q),fun q => u (n,true,q)⟩

theorem mapComplexBits_coeff (F : CompleteValueMap B C) (u : TaylorSlot → B) (n : ℕ) :
    mapComplexBits F (complexCoeffBits u n) = complexCoeffBits (fun q => F.toFun (u q)) n :=
  rfl

end JSP000930.Positive
