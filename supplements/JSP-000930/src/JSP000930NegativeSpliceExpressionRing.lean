import JSP000930NegativeNamedSpliceGuard

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.ExprPoly

open JSP000930.BooleanAnalysis

variable {V W B : Type} [NontrivialCompleteBooleanAlgebra B]

def patchTimes (p q : Poly V) : Poly V :=
  match p with
  | [] => []
  | a :: t => plus (scale a q) (zero :: patchTimes t q)

def patchMinus (p q : Poly V) : Poly V :=
  plus p (scale (Expr.neg one) q)

def patchPoly (p h g : Poly V) : Poly V :=
  plus p (patchTimes g (patchMinus h p))

private theorem patch_safe_zero (u : V → ComplexBits B) (m : B) :
    (zero : Expr V).Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

theorem patchTimes_safe {u : V → ComplexBits B} {m : B} {p q : Poly V}
    (hp : CoeffSafe u m p) (hq : CoeffSafe u m q) : CoeffSafe u m (patchTimes p q) := by
  induction p with
  | nil => intro c hc; exact (List.not_mem_nil hc).elim
  | cons a p ih =>
    apply coeffSafe_plus (coeffSafe_scale (hp a List.mem_cons_self) hq)
    intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact patch_safe_zero u m
    · exact ih (fun c hc => hp c (List.mem_cons_of_mem _ hc)) d hd

theorem patchPoly_safe {u : V → ComplexBits B} {m : B} {p h g : Poly V}
    (hp : CoeffSafe u m p) (hh : CoeffSafe u m h) (hg : CoeffSafe u m g) :
    CoeffSafe u m (patchPoly p h g) := by
  have hN : (Expr.neg (one : Expr V)).Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  exact coeffSafe_plus hp (patchTimes_safe hg (coeffSafe_plus hh (coeffSafe_scale hN hp)))

theorem atExpr_patchTimes (p q : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr (patchTimes p q) z).evalGround x =
      (atExpr p z).evalGround x * (atExpr q z).evalGround x := by
  induction p with
  | nil =>
    change (zero : Expr V).evalGround x = zero.evalGround x * (atExpr q z).evalGround x
    simp only [ground_zero,zero_mul]
  | cons a p ih =>
    rw [patchTimes,atExpr_plus,atExpr_scale]
    change a.evalGround x * (atExpr q z).evalGround x +
      ((zero : Expr V).evalGround x + z.evalGround x * (atExpr (patchTimes p q) z).evalGround x) =
      (a.evalGround x + z.evalGround x * (atExpr p z).evalGround x) * (atExpr q z).evalGround x
    rw [ih,ground_zero]
    ring

theorem atExpr_patchPoly (p h g : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr (patchPoly p h g) z).evalGround x =
      (atExpr p z).evalGround x + (atExpr g z).evalGround x *
        ((atExpr h z).evalGround x - (atExpr p z).evalGround x) := by
  rw [patchPoly,atExpr_plus,atExpr_patchTimes,patchMinus,atExpr_plus,atExpr_scale]
  change _ + _ * (_ + -((one : Expr V).evalGround x) * _) = _
  rw [ground_one]
  ring

theorem patchPlus_rename (f : V → W) (p q : Poly V) :
    (plus p q).map (Expr.rename f) = plus (p.map (Expr.rename f)) (q.map (Expr.rename f)) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      change Expr.add (a.rename f) (b.rename f) :: (plus p q).map (Expr.rename f) =
        Expr.add (a.rename f) (b.rename f) :: plus (p.map (Expr.rename f)) (q.map (Expr.rename f))
      rw [ih]

theorem patchScale_rename (f : V → W) (a : Expr V) (p : Poly V) :
    (scale a p).map (Expr.rename f) = scale (a.rename f) (p.map (Expr.rename f)) := by
  simp only [scale,List.map_map]
  rfl

theorem patchTimes_rename (f : V → W) (p q : Poly V) :
    (patchTimes p q).map (Expr.rename f) = patchTimes (p.map (Expr.rename f)) (q.map (Expr.rename f)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [patchTimes,List.map_cons,patchPlus_rename,patchScale_rename,ih] <;> rfl

theorem patchPoly_rename (f : V → W) (p h g : Poly V) :
    (patchPoly p h g).map (Expr.rename f) =
      patchPoly (p.map (Expr.rename f)) (h.map (Expr.rename f)) (g.map (Expr.rename f)) := by
  simp only [patchPoly,patchMinus,patchPlus_rename,patchScale_rename,patchTimes_rename] <;> rfl

end JSP000930.Negative.ExprPoly
