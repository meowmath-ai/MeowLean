import JSP000930AnalyticNaturalExpr

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_NatExpr_compare_checked {n k : ℕ} (v : DVec (V B) n)
    (p : Fin k → STerm n) (q : Fin k → ℕ) (e f : NatExpr k)
    (cmp : ∀ {d : ℕ}, STerm d → STerm d → SForm d) (test : ℕ → ℕ → Prop)
    (hp : ∀ i, bTerm v (p i) = bSet.of_nat (q i))
    (hcmp : ∀ {d : ℕ} (w : DVec (V B) d) (a b : STerm d) (x y : ℕ),
      bTerm w a = bSet.of_nat x → bTerm w b = bSet.of_nat y →
      bTruth w (cmp a b) = crispTruth B (test x y)) :
    bTruth v (e.compare_f cmp f p) = crispTruth B (test (e.val q) (f.val q)) := by
  let x0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let y0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let w (i j : ℕ) : DVec (V B) (n+2) :=
    DVec.cons (bSet.of_nat j) (DVec.cons (bSet.of_nat i) v)
  have hval (i j : ℕ) (z : Fin k) :
      bTerm (w i j) (up2 (p z)) = bSet.of_nat (q z) :=
    (bTerm_up2_r181 v (bSet.of_nat i) (bSet.of_nat j) (p z)).trans (hp z)
  have hx (i j : ℕ) : bTerm (w i j) (up x0) = bSet.of_nat i :=
    (bTerm_up_r181 (DVec.cons (bSet.of_nat i) v) (bSet.of_nat j) x0).trans
      (bTerm_current_r181 v (bSet.of_nat i))
  have hy (i j : ℕ) : bTerm (w i j) y0 = bSet.of_nat j :=
    bTerm_current_r181 (DVec.cons (bSet.of_nat i) v) (bSet.of_nat j)
  simp only [NatExpr.compare_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ i : ℕ, ⨆ j : ℕ, bTruth (w i j) (e.rel_f (fun z => up2 (p z)) (up x0)) ⊓
    (bTruth (w i j) (f.rel_f (fun z => up2 (p z)) y0) ⊓
       bTruth (w i j) (cmp (up x0) y0))) = _
  have hE (i j : ℕ) := bTruth_NatExpr_checked e (w i j) (fun z => up2 (p z))
    (up x0) q i (hval i j) (hx i j)
  have hF (i j : ℕ) := bTruth_NatExpr_checked f (w i j) (fun z => up2 (p z))
    y0 q j (hval i j) (hy i j)
  have hC (i j : ℕ) := hcmp (w i j) (up x0) y0 i j (hx i j) (hy i j)
  simp only [hE,hF,hC,← inf_iSup_eq,iSup_crispEquality_select_r193]

end JSP000930.AnalyticSyntax
