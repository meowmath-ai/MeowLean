import JSP000930PositiveCanonicalCutsForceLiteralSequence

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000933.BooleanNames
  JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem canonical_sequence_bits_mask {n : ℕ}
    (v : DVec (V B) n) (A : STerm n) (U : TaylorSlot → B) (p : B)
    (hT : bTerm v A = taylorCodeName U) (hSeq : p ≤ bTruth v (sequence_f A)) :
    ∀ i,sameMaskedComplex p (sequenceBits (bTerm v A) i) (complexCoeffBits U i) := by
  obtain ⟨hF,hC,hM⟩ := sequenceBits_actual v A p hSeq
  have hb (i : ℕ) (b : Bool) (q : RatPresentation) :
      p ⊓ graphTaylorBits (bTerm v A) (i,b,q) = p ⊓ U (i,b,q) := by
    let x := weightedRationalSet (fun r => U (i,false,r))
    let y := weightedRationalSet (fun r => U (i,true,r))
    have hp : p ≤ pair (bSet.of_nat i) (pair x y) ∈ᴮ bTerm v A := by
      rw [hT,taylorCodeName_at U i]
      exact bv_refl
    have h := graphTaylorBits_on_pair (bTerm v A) i x y p hF hp b q
    cases b
    · simpa [x,ratName_mem_weightedRationalSet] using h
    · simpa [y,ratName_mem_weightedRationalSet] using h
  exact fun i => ⟨fun q => hb i false q,fun q => hb i true q⟩

theorem canonical_native_data_forces_entire {n : ℕ}
    (v : DVec (V B) n) (A : STerm n) (U : TaylorSlot → B) (p : B)
    (hT : bTerm v A = taylorCodeName U)
    (hCuts : ∀ i,(complexCoeffBits U i).CutOn p)
    (hG : GrowthOn p (complexCoeffBits U)) :
    p ≤ bTruth v (isEntireCode_f A) := by
  have hSeq := forces_literal_sequence_of_canonical_cuts v A U p hT hCuts
  have hEq := canonical_sequence_bits_mask v A U p hT hSeq
  have hMask := masked_growthValue_congr (p := p) (U := sequenceBits (bTerm v A))
    (V := complexCoeffBits U) (fun i => (hEq i).1) (fun i => (hEq i).2)
  have hG' : GrowthOn p (sequenceBits (bTerm v A)) := by
    apply (growthValue_le_iff _ _).1
    exact (le_inf le_rfl ((growthValue_le_iff _ _).2 hG)).trans
      (hMask.ge.trans inf_le_right)
  unfold isEntireCode_f
  rw [bTruth_and_eq]
  exact le_inf hSeq ((forces_entireRadii_iff v A p hSeq).2 hG')

end JSP000930.Positive
