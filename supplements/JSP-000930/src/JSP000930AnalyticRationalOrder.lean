import JSP000930AnalyticArithmeticCompare
import JSP000930AnalyticRoundedLimit

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_crossOrder_checked {n : ℕ} (v : DVec (V B) n)
    (p m d q r s : STerm n) (x y : RatPresentation)
    (hp : bTerm v p = bSet.of_nat x.pos)
    (hm : bTerm v m = bSet.of_nat x.neg)
    (hd : bTerm v d = bSet.of_nat x.den)
    (hq : bTerm v q = bSet.of_nat y.pos)
    (hr : bTerm v r = bSet.of_nat y.neg)
    (hs : bTerm v s = bSet.of_nat y.den) :
    bTruth v (crossOrder_f p m d q r s) = crispTruth B (x.value ≤ y.value) := by
  let params : Fin 6 → STerm n := ![p,m,d,q,r,s]
  let raw : Fin 6 → ℕ := ![x.pos,x.neg,x.den,y.pos,y.neg,y.den]
  have hparams (i : Fin 6) : bTerm v (params i) = bSet.of_nat (raw i) := by
    fin_cases i
    · exact hp
    · exact hm
    · exact hd
    · exact hq
    · exact hr
    · exact hs
  let L : NatExpr 6 := .add (.mul (.var 0) (.var 5)) (.mul (.var 4) (.var 2))
  let R : NatExpr 6 := .add (.mul (.var 3) (.var 2)) (.mul (.var 1) (.var 5))
  change bTruth v (L.compare_f natLE_f R params) = _
  rw [bTruth_NatExpr_compare_checked v params raw L R natLE_f (· ≤ ·) hparams
    (fun w a b k j ha hb => bTruth_natLE_checked_r192 w a b k j ha hb),
    ratPresentation_cross_le x y] <;> rfl

theorem bTruth_rationalLE_named {n : ℕ} (v : DVec (V B) n) (u w : STerm n)
    (x y : RatPresentation) (hu : bTerm v u = ratName x) (hw : bTerm v w = ratName y) :
    bTruth v (rationalLE_f u w) = crispTruth B (x.value ≤ y.value) := by
  let v1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat x.pos) v
  let v2 : DVec (V B) (n+2) := DVec.cons (bSet.of_nat x.neg) v1
  let v3 : DVec (V B) (n+3) := DVec.cons (bSet.of_nat x.den) v2
  let v4 : DVec (V B) (n+4) := DVec.cons (bSet.of_nat y.pos) v3
  let v5 : DVec (V B) (n+5) := DVec.cons (bSet.of_nat y.neg) v4
  let v6 : DVec (V B) (n+6) := DVec.cons (bSet.of_nat y.den) v5
  let a : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let b : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let d : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let e : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let f : STerm (n+5) := bd_var ⟨0,Nat.succ_pos (n+4)⟩
  let g : STerm (n+6) := bd_var ⟨0,Nat.succ_pos (n+5)⟩
  have hw' : bTerm v3 (up3 w) = ratName y :=
    (bTerm_up3_r181 v (bSet.of_nat x.pos) (bSet.of_nat x.neg) (bSet.of_nat x.den) w).trans hw
  unfold rationalLE_f
  rw [bTruth_unpackRational_named v u (fun _ : Fin 1 => w) _ x hu]
  change bTruth v3 (unpackRational_f (up3 w) (fun i => ![up2 a,up b,d] i)
    (fun ps e0 f0 g0 => crossOrder_f (ps 0) (ps 1) (ps 2) e0 f0 g0)) = _
  rw [bTruth_unpackRational_named v3 (up3 w) (fun i => ![up2 a,up b,d] i) _ y hw']
  change bTruth v6 (crossOrder_f (up3 (up2 a)) (up3 (up b)) (up3 d) (up2 e) (up f) g) = _
  apply bTruth_crossOrder_checked v6 _ _ _ _ _ _ x y
  all_goals simp only [v6,v5,v4,v3,v2,v1,a,b,d,e,f,g,
    bTerm_up3_r181,bTerm_up2_r181,bTerm_up_r181,bTerm_current_r181]
  all_goals rfl

theorem bTruth_rationalLT_named {n : ℕ} (v : DVec (V B) n) (u w : STerm n)
    (x y : RatPresentation) (hu : bTerm v u = ratName x) (hw : bTerm v w = ratName y) :
    bTruth v (rationalLT_f u w) = crispTruth B (x.value < y.value) := by
  simp only [rationalLT_f, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_not, bTruth_rationalLE_named v u w x y hu hw,
    bTruth_rationalLE_named v w u y x hw hu]
  rcases lt_trichotomy x.value y.value with h | h | h
  · simp [crispTruth,h,h.le,not_le_of_gt h]
  · simp [crispTruth,h]
  · simp [crispTruth,h.le,not_le_of_gt h,not_lt_of_gt h]

end JSP000930.AnalyticSyntax
