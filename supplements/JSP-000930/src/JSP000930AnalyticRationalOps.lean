import JSP000930AnalyticArithmeticCompare
import JSP000930AnalyticRationalCross

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def rawPresentationThree (x y z : RatPresentation) : Fin 9 → ℕ :=
  ![x.pos,x.neg,x.den,y.pos,y.neg,y.den,z.pos,z.neg,z.den]

theorem bTruth_rationalTernary_checked {n : ℕ} (v : DVec (V B) n)
    (X Y Z : STerm n)
    (M : ∀ {d : ℕ}, (Fin 9 → STerm d) → SForm d)
    (test : RatPresentation → RatPresentation → RatPresentation → Prop)
    (x y z : RatPresentation)
    (hX : bTerm v X = ratName x) (hY : bTerm v Y = ratName y) (hZ : bTerm v Z = ratName z)
    (hM : ∀ {d : ℕ} (env : DVec (V B) d) (p : Fin 9 → STerm d)
        (ht : ∀ i, bTerm env (p i) = bSet.of_nat (rawPresentationThree x y z i)),
      bTruth env (M p) = crispTruth B (test x y z)) :
    bTruth v (rationalTernary_f X Y Z M) = crispTruth B (test x y z) := by
  let v1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat x.pos) v
  let v2 : DVec (V B) (n+2) := DVec.cons (bSet.of_nat x.neg) v1
  let v3 : DVec (V B) (n+3) := DVec.cons (bSet.of_nat x.den) v2
  let v4 : DVec (V B) (n+4) := DVec.cons (bSet.of_nat y.pos) v3
  let v5 : DVec (V B) (n+5) := DVec.cons (bSet.of_nat y.neg) v4
  let v6 : DVec (V B) (n+6) := DVec.cons (bSet.of_nat y.den) v5
  let v7 : DVec (V B) (n+7) := DVec.cons (bSet.of_nat z.pos) v6
  let v8 : DVec (V B) (n+8) := DVec.cons (bSet.of_nat z.neg) v7
  let v9 : DVec (V B) (n+9) := DVec.cons (bSet.of_nat z.den) v8
  let a : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let b : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let d : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let e : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let f : STerm (n+5) := bd_var ⟨0,Nat.succ_pos (n+4)⟩
  let g : STerm (n+6) := bd_var ⟨0,Nat.succ_pos (n+5)⟩
  let h : STerm (n+7) := bd_var ⟨0,Nat.succ_pos (n+6)⟩
  let j : STerm (n+8) := bd_var ⟨0,Nat.succ_pos (n+7)⟩
  let k : STerm (n+9) := bd_var ⟨0,Nat.succ_pos (n+8)⟩
  have hy : bTerm v3 (up3 Y) = ratName y :=
    (bTerm_up3_r181 v (bSet.of_nat x.pos) (bSet.of_nat x.neg) (bSet.of_nat x.den) Y).trans hY
  have hz : bTerm v6 (up3 (up3 Z)) = ratName z :=
    (bTerm_up3_r181 v3 (bSet.of_nat y.pos) (bSet.of_nat y.neg) (bSet.of_nat y.den) (up3 Z)).trans
      ((bTerm_up3_r181 v (bSet.of_nat x.pos) (bSet.of_nat x.neg) (bSet.of_nat x.den) Z).trans hZ)
  unfold rationalTernary_f
  rw [bTruth_unpackRational_named v X (fun i => ![Y,Z] i) _ x hX]
  change bTruth v3 (unpackRational_f (up3 Y)
    (fun i => ![up2 a,up b,d,up3 Z] i) (fun px e0 f0 g0 =>
      unpackRational_f (px 3) (fun i => ![px 0,px 1,px 2,e0,f0,g0] i)
        (fun py h0 j0 k0 => M (fun i => ![py 0,py 1,py 2,py 3,py 4,py 5,h0,j0,k0] i)))) = _
  rw [bTruth_unpackRational_named v3 (up3 Y)
    (fun i => ![up2 a,up b,d,up3 Z] i) _ y hy]
  change bTruth v6 (unpackRational_f (up3 (up3 Z))
    (fun i => ![up3 (up2 a),up3 (up b),up3 d,up2 e,up f,g] i)
      (fun py h0 j0 k0 => M (fun i => ![py 0,py 1,py 2,py 3,py 4,py 5,h0,j0,k0] i))) = _
  rw [bTruth_unpackRational_named v6 (up3 (up3 Z))
    (fun i => ![up3 (up2 a),up3 (up b),up3 d,up2 e,up f,g] i) _ z hz]
  let P : Fin 9 → STerm (n+9) :=
    ![up3 (up3 (up2 a)),up3 (up3 (up b)),up3 (up3 d),
      up3 (up2 e),up3 (up f),up3 g,up2 h,up j,k]
  change bTruth v9 (M P) = _
  apply hM v9 P
  intro i
  fin_cases i <;> simp [P,rawPresentationThree,v1,v2,v3,v4,v5,v6,v7,v8,v9,a,b,d,e,f,g,h,j,k,
    bTerm_up3_r181,bTerm_up2_r181,bTerm_up_r181,bTerm_current_r181]
  all_goals rfl

private theorem checked_equal {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (u w : ℕ) (ha : bTerm v a = bSet.of_nat u) (hb : bTerm v b = bSet.of_nat w) :
    bTruth v (bd_equal a b) = crispTruth B (u = w) := by
  simp only [bTruth_equal_r181,ha,hb,checkedNat_eq_crisp_r189]

theorem bTruth_rationalAdd_named {n : ℕ} (v : DVec (V B) n)
    (X Y Z : STerm n) (x y z : RatPresentation)
    (hX : bTerm v X = ratName x) (hY : bTerm v Y = ratName y) (hZ : bTerm v Z = ratName z) :
    bTruth v (rationalAdd_f X Y Z) = crispTruth B (x.value + y.value = z.value) := by
  unfold rationalAdd_f
  refine bTruth_rationalTernary_checked v X Y Z crossAdd_f
    (fun u w t => u.value+w.value=t.value) x y z hX hY hZ ?_
  intro d env p hp
  unfold crossAdd_f
  rw [bTruth_NatExpr_compare_checked env p (rawPresentationThree x y z) _ _
    bd_equal (· = ·) hp checked_equal, ratPresentation_cross_add] <;> rfl

theorem bTruth_rationalMul_named {n : ℕ} (v : DVec (V B) n)
    (X Y Z : STerm n) (x y z : RatPresentation)
    (hX : bTerm v X = ratName x) (hY : bTerm v Y = ratName y) (hZ : bTerm v Z = ratName z) :
    bTruth v (rationalMul_f X Y Z) = crispTruth B (x.value * y.value = z.value) := by
  unfold rationalMul_f
  refine bTruth_rationalTernary_checked v X Y Z crossMul_f
    (fun u w t => u.value*w.value=t.value) x y z hX hY hZ ?_
  intro d env p hp
  unfold crossMul_f
  rw [bTruth_NatExpr_compare_checked env p (rawPresentationThree x y z) _ _
    bd_equal (· = ·) hp checked_equal, ratPresentation_cross_mul] <;> rfl

end JSP000930.AnalyticSyntax
