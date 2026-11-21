import JSP000930PositiveCanonicalEntireMatchesNativeCode
import JSP000930PositiveLiteralConditionalPositiveEndpoint

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis
  JSP000930.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem weighted_complexName_forces_complex {n : ℕ} (v : DVec (V B) n) (Z : STerm n)
    (u : ComplexBits B) (p : B) (hZ : bTerm v Z = u.name) (hu : u.CutOn p) :
    p ≤ bTruth v (complex_f Z) := by
  have hCoords := forces_weightedComplex_coordinates v u.re u.im
  let w := complexCoordinates v (weightedRationalSet u.re) (weightedRationalSet u.im)
  have hR := (forces_realCut_weighted_iff w realCoordinate_f u.re hCoords.1 p).2 hu.1
  have hI := (forces_realCut_weighted_iff w imagCoordinate_f u.im hCoords.2 p).2 hu.2
  refine forces_complex_pair_of_weightedCuts v Z u.re u.im p ?_ hR hI
  rw [hZ]
  exact bv_refl

theorem literal_family_member_native_data {n : ℕ} (v : DVec (V B) n) (F : STerm n)
    (U : TaylorSlot → B) (p : B)
    (hF : p ≤ bTruth v (familyEntire_f actualAnalyticSyntax F))
    (hM : p ≤ taylorCodeName U ∈ᴮ bTerm v F) :
    (p ≤ is_func (taylorCodeName U)) ∧
      (∀ i,(sequenceBits (taylorCodeName U) i).CutOn p) ∧
      (∀ i,p ≤ pair (bSet.of_nat i) (sequenceBits (taylorCodeName U) i).name ∈ᴮ taylorCodeName U) ∧
      GrowthOn p (sequenceBits (taylorCodeName U)) ∧
      (∀ i,(complexCoeffBits U i).CutOn p) ∧ GrowthOn p (complexCoeffBits U) ∧
      (∀ i,sameMaskedComplex p (sequenceBits (taylorCodeName U) i) (complexCoeffBits U i)) := by
  let a := taylorCodeName U
  let w : DVec (V B) (n+1) := DVec.cons a v
  let A : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hE : p ≤ bTruth w (isEntireCode_f A) :=
    (le_inf le_rfl hM).trans (with_familyEntire_member v F a p hF)
  have hR : bTerm w A = a := bTerm_current_r181 v a
  have hs : p ≤ bTruth w (sequence_f A) := by
    have hp := hE
    unfold isEntireCode_f at hp
    rw [bTruth_and_eq] at hp
    exact hp.trans inf_le_left
  obtain ⟨hf,hc,hm⟩ := sequenceBits_actual w A p hs
  have hg := entire_growthOn w A p hE
  obtain ⟨hc',hg',hAgree⟩ := canonical_named_entire_native_data w A U p hR hE
  rw [hR] at hf hc hm hg hAgree
  exact ⟨hf,hc,hm,hg,hc',hg',hAgree⟩

end JSP000930.Positive
