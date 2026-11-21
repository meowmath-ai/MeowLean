import JSP000930AnalyticComplexAdd

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_selectMul_weighted {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i j : Fin k) (u w : RatPresentation → B) (p : B)
    (hi : bTerm v (ps i) = weightedRationalSet u)
    (hj : bTerm v (ps j) = weightedRationalSet w)
    (hu : ProperCutOn p u) (hw : ProperCutOn p w) :
    let V : DVec (V B) (n+1) := DVec.cons (mulCutName u w) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps (fun a r => realMul_f (a i) (a j) r) D) =
      p ⊓ bTruth V (D (fun a => up (ps a)) T) := by
  apply bTruth_selectReal_weighted v ps (fun a r => realMul_f (a i) (a j) r) D
    (mulCutBits u w) p (mulCutBits_properCut u w p hu hw)
  intro t
  let x := weightedRationalSet t
  let V := DVec.cons x v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  exact bTruth_realMul_weighted V (up (ps i)) (up (ps j)) T u w t
    ((bTerm_up_r181 v x (ps i)).trans hi) ((bTerm_up_r181 v x (ps j)).trans hj)
    (bTerm_current_r181 v x)

theorem bTruth_selectNeg_weighted {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i : Fin k) (u : RatPresentation → B) (p : B)
    (hi : bTerm v (ps i) = weightedRationalSet u) (hu : ProperCutOn p u) :
    let V : DVec (V B) (n+1) := DVec.cons (negCutName u) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps (fun a r => realNeg_f (a i) r) D) =
      p ⊓ bTruth V (D (fun a => up (ps a)) T) := by
  apply bTruth_selectReal_weighted v ps (fun a r => realNeg_f (a i) r) D
    (negCutBits u) p (negCutBits_properCut u p hu)
  intro t
  let x := weightedRationalSet t
  let V := DVec.cons x v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  exact bTruth_realNeg_weighted V (up (ps i)) T u t
    ((bTerm_up_r181 v x (ps i)).trans hi) (bTerm_current_r181 v x)

end JSP000930.AnalyticSyntax
