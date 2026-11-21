import JSP000930PositiveRationalCertificateTransport
import JSP000930AnalyticRealAxisName

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Positive.Cohen

open JSP000933.SetLanguage JSP000933.OpenGraphForcing
  JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax

noncomputable def reservePoint (c : OmegaOneIndex) : bSet WetzelCohenBA :=
  bSet.pair (dyadicCutName (B := JSP000933.PreparedModel.PreparedBA) (Sum.inr c : WetzelRow))
    (weightedRationalSet (checkedRealBits 0))

theorem reserveRow_fresh (c : OmegaOneIndex) (n : ℕ) :
    ((Sum.inr c : WetzelRow),n) ∉ reservePrefix c := by
  change ¬ c < c
  exact lt_irrefl c

theorem dyadicCut_is_proper
    {B I : Type} [NontrivialCompleteBooleanAlgebra B]
    (i : I) :
    ProperCutOn (⊤ : CohenBA B (I × ℕ)) (dyadicCutBits (B := B) i) := by
  let v : DVec (V (CohenBA B (I × ℕ))) 0 := DVec.nil
  let w : DVec (V (CohenBA B (I × ℕ))) 1 :=
    DVec.cons (dyadicCutName (B := B) i) v
  let X : STerm 1 := bd_var ⟨0,by decide⟩
  have hX : bTerm w X = weightedRationalSet (dyadicCutBits (B := B) i) :=
    bTerm_current_r181 v (dyadicCutName (B := B) i)
  exact (forces_realCut_weighted_iff w X (dyadicCutBits (B := B) i) hX ⊤).mp
    (dyadicCut_forces_realCut v i)

theorem reservePoint_forces_complex {n : ℕ}
    (v : DVec (V WetzelCohenBA) n) (Z : STerm n)
    (c : OmegaOneIndex) (hZ : bTerm v Z = reservePoint c) :
    (⊤ : WetzelCohenBA) ≤ bTruth v (complex_f Z) :=
  forces_complex_realAxis v Z
    (dyadicCutBits (B := JSP000933.PreparedModel.PreparedBA) (Sum.inr c : WetzelRow))
    (dyadicCut_is_proper (Sum.inr c : WetzelRow)) hZ

end JSP000930.Positive.Cohen
