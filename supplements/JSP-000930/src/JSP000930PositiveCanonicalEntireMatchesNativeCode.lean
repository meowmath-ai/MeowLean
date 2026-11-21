import JSP000930PositiveActualFreshNativeReserveSeparation
import JSP000930AnalyticEntireGrowth

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000933.BooleanNames
  JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem canonical_named_entire_native_data {n : ℕ}
    (v : DVec (V B) n) (A : STerm n) (U : TaylorSlot → B) (p : B)
    (hTerm : bTerm v A = taylorCodeName U)
    (hEntire : p ≤ bTruth v (isEntireCode_f A)) :
    (∀ i,(complexCoeffBits U i).CutOn p) ∧
      GrowthOn p (complexCoeffBits U) ∧
      ∀ i,sameMaskedComplex p (sequenceBits (bTerm v A) i) (complexCoeffBits U i) := by
  have hSeq : p ≤ bTruth v (sequence_f A) := by
    unfold isEntireCode_f at hEntire
    rw [bTruth_and_eq] at hEntire
    exact hEntire.trans inf_le_left
  obtain ⟨hF,hCut,hMem⟩ := sequenceBits_actual v A p hSeq
  have hMask (i : ℕ) (b : Bool) (q : RatPresentation) :
      p ⊓ graphTaylorBits (bTerm v A) (i,b,q) = p ⊓ U (i,b,q) := by
    let x := weightedRationalSet (fun r => U (i,false,r))
    let y := weightedRationalSet (fun r => U (i,true,r))
    have hp : p ≤ pair (bSet.of_nat i) (pair x y) ∈ᴮ bTerm v A := by
      rw [hTerm]
      exact le_top.trans (pair_mem_functionalGraph_self_r102 bSet.of_nat (coefficientName U) i)
    have h := graphTaylorBits_on_pair (bTerm v A) i x y p hF hp b q
    cases b
    · simpa [x,ratName_mem_weightedRationalSet] using h
    · simpa [y,ratName_mem_weightedRationalSet] using h
  have hA (i : ℕ) : sameMaskedComplex p (sequenceBits (bTerm v A) i) (complexCoeffBits U i) :=
    ⟨fun q => hMask i false q,fun q => hMask i true q⟩
  refine ⟨fun i => ⟨properCutOn_of_same_mask (hCut i).1 (hA i).1,
    properCutOn_of_same_mask (hCut i).2 (hA i).2⟩,?_ ,hA⟩
  have hGr := entire_growthOn v A p hEntire
  have hV := masked_growthValue_congr (p := p) (U := sequenceBits (bTerm v A))
    (V := complexCoeffBits U) (fun i => (hA i).1) (fun i => (hA i).2)
  apply (growthValue_le_iff _ _).1
  exact (le_inf le_rfl ((growthValue_le_iff _ _).2 hGr)).trans (hV.le.trans inf_le_right)

end JSP000930.Positive
