import JSP000930NegativeNamedPaletteScheduleCardinals
import JSP000930PositiveCanonicalNativeGrowthForcesLiteralEntire
import JSP000930AnalyticLiteralEvaluation

open Fol bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.SetLanguage JSP000933.BooleanNames JSP000930.Positive
  JSP000930.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedPaletteSchedule.family_forces_entire {n : ℕ}
    (S : NamedPaletteSchedule B) (v : DVec (V B) n) (F : STerm n)
    (hF : bTerm v F = S.family) :
    (⊤ : B) ≤ bTruth v (familyEntire_f actualAnalyticSyntax F) := by
  unfold familyEntire_f
  rw [bTruth_allIn_r181,hF]
  apply le_iInf
  intro a
  rw [← _root_.deduction,top_inf_eq]
  simp only [NamedPaletteSchedule.family,mem_familyName_r70,top_inf_eq]
  apply iSup_le
  intro i
  let x := taylorCodeName (S.code i)
  let A : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let φ : SForm (n+1) := isEntireCode_f A
  have hx : (⊤ : B) ≤ bTruth (DVec.cons x v) φ :=
    canonical_native_data_forces_entire _ A (S.code i) ⊤
      (bTerm_current_r181 v x) (S.codeCut i) (S.codeGrowth i)
  exact (le_inf (bv_symm le_rfl) (le_top.trans hx)).trans
    (bTruth_body_ext_r191 v φ x a)

theorem canonical_evalAt_iff_native {n : ℕ}
    (v : DVec (V B) n) (A Z Y : STerm n) (U : TaylorSlot → B) (z : ComplexBits B) (p : B)
    (hA : bTerm v A = taylorCodeName U) (hZ : bTerm v Z = z.name)
    (hCut : ∀ i,(complexCoeffBits U i).CutOn p) (hG : GrowthOn p (complexCoeffBits U))
    (hz : z.CutOn p) :
    p ≤ bTruth v (evalAt_f A Z Y) ↔ p ≤ bTerm v Y =ᴮ
      (taylorLimitBits (complexCoeffBits U) z).name := by
  have hEntire := canonical_native_data_forces_entire v A U p hA hCut hG
  have hSeq := forces_literal_sequence_of_canonical_cuts v A U p hA hCut
  have hAgree := canonical_sequence_bits_mask v A U p hA hSeq
  have hNative : p ≤ (taylorLimitBits (sequenceBits (bTerm v A)) z).name =ᴮ
      (taylorLimitBits (complexCoeffBits U) z).name :=
    sameMaskedComplex_name (sameMaskedComplex_taylorLimit hAgree (sameMaskedComplex_self p z))
  have h := (literalTaylorEvalCorrespondence (B := B)).agrees v A Z Y z p hZ hz hEntire
  exact h.trans ⟨fun he => bv_trans he hNative,fun he => bv_trans he (bv_symm hNative)⟩

end JSP000930.Negative
