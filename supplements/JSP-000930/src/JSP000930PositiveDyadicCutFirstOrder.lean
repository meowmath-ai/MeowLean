import JSP000930PositiveActualDyadicCutName
import JSP000930AnalyticValidCutBridge

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Positive.Cohen

open JSP000933.SetLanguage JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem dyadicCut_forces_realCut {n : ℕ}
    (v : DVec (V (CohenBA B (I × ℕ))) n) (i : I) :
    let w : DVec (V (CohenBA B (I × ℕ))) (n+1) :=
      DVec.cons (dyadicCutName (B := B) i) v
    let X : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    (⊤ : CohenBA B (I × ℕ)) ≤ bTruth w (realCut_f X) := by
  let w : DVec (V (CohenBA B (I × ℕ))) (n+1) :=
    DVec.cons (dyadicCutName (B := B) i) v
  let X : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  change (⊤ : CohenBA B (I × ℕ)) ≤ bTruth w (realCut_f X)
  have hX : bTerm w X = weightedRationalSet (dyadicCutBits (B := B) i) :=
    bTerm_current_r181 v (dyadicCutName (B := B) i)
  apply (forces_realCut_weighted_iff w X (dyadicCutBits (B := B) i) hX ⊤).mpr
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨q,hq⟩ := ratPresentation_value_surjective (-1)
    have hq' : q.value < 0 := by rw [hq]; norm_num
    exact (dyadicCutBits_all_negative (B := B) i q hq').ge.trans (le_iSup (dyadicCutBits (B := B) i) q)
  · obtain ⟨q,hq⟩ := ratPresentation_value_surjective 1
    have hq' : 1 ≤ q.value := by rw [hq]
    apply le_iSup_of_le q
    rw [dyadicCutBits_no_above_one (B := B) i q hq',compl_bot]
  · intro q r h
    exact inf_le_right.trans (dyadicCutBits_downward (B := B) i h)
  · intro q
    exact inf_le_right.trans_eq (dyadicCutBits_rounded (B := B) i q)

end JSP000930.Positive.Cohen
