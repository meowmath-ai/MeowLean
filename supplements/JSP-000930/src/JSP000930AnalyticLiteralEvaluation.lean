import JSP000930AnalyticNativeEvaluation
import JSP000930PositiveExactEvalCorrespondenceInterface

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem forces_evalAt_iff_taylorLimit {n : ℕ} (v : DVec (V B) n)
    (A Z Y : STerm n) (z : ComplexBits B) (p : B)
    (hZ : bTerm v Z = z.name) (hz : z.CutOn p)
    (hEntire : p ≤ bTruth v (isEntireCode_f A)) :
    p ≤ bTruth v (evalAt_f A Z Y) ↔
      p ≤ bTerm v Y =ᴮ (taylorLimitBits (sequenceBits (bTerm v A)) z).name := by
  have hSeq : p ≤ bTruth v (sequence_f A) := by
    have h := hEntire
    simp only [isEntireCode_f,boolean_realize_bounded_formula_and] at h
    exact h.trans inf_le_left
  let a := sequenceBits (bTerm v A)
  obtain ⟨hf,ha,hval⟩ := sequenceBits_actual v A p hSeq
  have hg : GrowthOn p a := entire_growthOn v A p hEntire
  let u := taylorLimitBits a z
  have hU : u.CutOn p := taylorLimitBits_cutOn a z p ha hz hg
  simp only [evalAt_f,boolean_realize_bounded_formula_and]
  constructor
  · intro h
    have hY : p ≤ bTruth v (complex_f Y) :=
      h.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hTail : p ≤ bTruth v (evalAllTail_f A Z Y) :=
      h.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    obtain ⟨w,hw,he⟩ := complexBits_of_forcedName v Y p hY
    have hNative := (forces_evalAllTail_iff v A Z Y a z w p hZ he ha hz hw hf hval).1 hTail
    exact bSet.bv_trans he (evalNative_unique ha hz hw hg hNative)
  · intro he
    refine le_inf hEntire (le_inf (forces_complexBits_name v Z z p hZ hz) (le_inf ?_ ?_))
    · exact forces_complex_pair_of_cutData v Y u.re u.im p he hU.1 hU.2
    · exact (forces_evalAllTail_iff v A Z Y a z u p hZ he ha hz hU hf hval).2
        (taylorLimitBits_evalNative a z p ha hz hg)

theorem literalTaylorEvalCorrespondence : JSP000930.Positive.LiteralTaylorEvalCorrespondence B where
  agrees v A Z Y z p hZ hz hEntire := forces_evalAt_iff_taylorLimit v A Z Y z p hZ hz hEntire

end JSP000930.AnalyticSyntax
