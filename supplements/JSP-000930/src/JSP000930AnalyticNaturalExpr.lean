import JSP000930AnalyticRationalBinders
import JSP000930AnalyticNaturalPower

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem bTruth_natRelBinary {n : ℕ} (v : DVec (V B) n) (op : NatOpF)
    (relA relB : ∀ {d : ℕ}, (STerm n → STerm d) → STerm d → SForm d) (out : STerm n)
    (A C D : ℕ) (f : ℕ → ℕ → ℕ)
    (ho : bTerm v out = bSet.of_nat D)
    (ha : ∀ (x y : ℕ),
      let w := DVec.cons (bSet.of_nat y : V B) (DVec.cons (bSet.of_nat x : V B) v)
      let ua : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
      bTruth w (relA up2 (up ua)) = crispTruth B (x=A))
    (hb : ∀ (x y : ℕ),
      let w := DVec.cons (bSet.of_nat y : V B) (DVec.cons (bSet.of_nat x : V B) v)
      let ub : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
      bTruth w (relB up2 ub) = crispTruth B (y=C))
    (hop : ∀ {d : ℕ} (w : DVec (V B) d) (a b c : STerm d) (x y z : ℕ),
      bTerm w a = bSet.of_nat x → bTerm w b = bSet.of_nat y → bTerm w c = bSet.of_nat z →
      bTruth w (op a b c) = crispTruth B (z=f x y)) :
    bTruth v (natRelBinary_f op relA relB out) = crispTruth B (D = f A C) := by
  let ua : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let ub : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let w (x y : ℕ) : DVec (V B) (n+2) :=
    DVec.cons (bSet.of_nat y) (DVec.cons (bSet.of_nat x) v)
  have hh (x y : ℕ) : bTruth (w x y) (op (up ua) ub (up2 out)) =
      crispTruth B (D = f x y) := by
    apply hop (w x y) (up ua) ub (up2 out) x y D
    · exact (bTerm_up_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y) ua).trans
        (bTerm_current_r181 v (bSet.of_nat x))
    · exact bTerm_current_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y)
    · exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) out).trans ho
  simp only [natRelBinary_f, bTruth_exOmega_r192, boolean_realize_bounded_formula_and]
  change (⨆ x : ℕ, ⨆ y : ℕ, bTruth (w x y) (relA up2 (up ua)) ⊓
      (bTruth (w x y) (relB up2 ub) ⊓ bTruth (w x y) (op (up ua) ub (up2 out)))) = _
  have ha' (x y : ℕ) : bTruth (w x y) (relA up2 (up ua)) = crispTruth B (x = A) := ha x y
  have hb' (x y : ℕ) : bTruth (w x y) (relB up2 ub) = crispTruth B (y = C) := hb x y
  simp only [ha', hb', hh, ← inf_iSup_eq, iSup_crispEquality_select_r193]

theorem bTruth_NatExpr_checked {n k : ℕ} (e : NatExpr k) (v : DVec (V B) n)
    (p : Fin k → STerm n) (out : STerm n) (q : Fin k → ℕ) (z : ℕ)
    (hp : ∀ i, bTerm v (p i) = bSet.of_nat (q i)) (hz : bTerm v out = bSet.of_nat z) :
    bTruth v (e.rel_f p out) = crispTruth B (z = e.val q) := by
  induction e generalizing n q z with
  | var i =>
    simp only [NatExpr.rel_f, NatExpr.val, bTruth_equal_r181, hz, hp i, checkedNat_eq_crisp_r189]
  | add a b iha ihb =>
    simp only [NatExpr.rel_f, NatExpr.val]
    apply bTruth_natRelBinary v addition_f _ _ out (a.val q) (b.val q) z (· + ·) hz
    · intro x y
      apply iha _ _ _ q x
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact (bTerm_up_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y) _).trans
          (bTerm_current_r181 v (bSet.of_nat x))
    · intro x y
      apply ihb _ _ _ q y
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact bTerm_current_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y)
    · exact bTruth_addition_checked_r196
  | mul a b iha ihb =>
    simp only [NatExpr.rel_f, NatExpr.val]
    apply bTruth_natRelBinary v multiplication_f _ _ out (a.val q) (b.val q) z (· * ·) hz
    · intro x y
      apply iha _ _ _ q x
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact (bTerm_up_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y) _).trans
          (bTerm_current_r181 v (bSet.of_nat x))
    · intro x y
      apply ihb _ _ _ q y
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact bTerm_current_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y)
    · exact bTruth_multiplication_checked_r196
  | pow a b iha ihb =>
    simp only [NatExpr.rel_f, NatExpr.val]
    apply bTruth_natRelBinary v naturalPow_f _ _ out (a.val q) (b.val q) z (· ^ ·) hz
    · intro x y
      apply iha _ _ _ q x
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact (bTerm_up_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y) _).trans
          (bTerm_current_r181 v (bSet.of_nat x))
    · intro x y
      apply ihb _ _ _ q y
      · intro i
        exact (bTerm_up2_r181 v (bSet.of_nat x) (bSet.of_nat y) (p i)).trans (hp i)
      · exact bTerm_current_r181 (DVec.cons (bSet.of_nat x) v) (bSet.of_nat y)
    · exact bTruth_naturalPow_checked

end JSP000930.AnalyticSyntax
