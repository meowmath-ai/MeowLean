import JSP000930FiniteExpressionSoundness

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

namespace ExprPoly

variable {V : Type}

abbrev Poly (V : Type) := List (Expr V)

def zero : Expr V := .num 0 0

def one : Expr V := .num 1 0

def plus : Poly V → Poly V → Poly V
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => .add a b :: plus p q

def scale (c : Expr V) (p : Poly V) : Poly V := p.map (Expr.mul c)

def linearMul (a : Expr V) (p : Poly V) : Poly V :=
  plus (zero :: p) (scale a.neg p)

def vanishing : List (Expr V) → Poly V
  | [] => [one]
  | a :: t => linearMul a (vanishing t)

def atExpr (p : Poly V) (z : Expr V) : Expr V :=
  p.foldr (fun c t => .add c (.mul z t)) zero

def displacement (p : Poly V) (old : List (Expr V)) (z y : Expr V) : Poly V :=
  let q := vanishing old
  let r := Expr.mul (.add y (.neg (atExpr p z))) (.inv (atExpr q z))
  plus p (scale r q)

open scoped BigOperators

@[simp] theorem ground_zero (x : V → ℂ) : (zero : Expr V).evalGround x = 0 := by
  apply Complex.ext <;> norm_num [zero,Expr.evalGround]

@[simp] theorem ground_one (x : V → ℂ) : (one : Expr V).evalGround x = 1 := by
  apply Complex.ext <;> norm_num [one,Expr.evalGround]

theorem ground_atExpr (p : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr p z).evalGround x =
      scalarPolynomialEval (p.map (fun a => a.evalGround x)) (z.evalGround x) := by
  induction p with
  | nil =>
    exact ground_zero x
  | cons a t ih =>
    change a.evalGround x + z.evalGround x * (atExpr t z).evalGround x =
      a.evalGround x + z.evalGround x *
        scalarPolynomialEval (t.map (fun a => a.evalGround x)) (z.evalGround x)
    rw [ih]

theorem atExpr_plus (p q : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr (plus p q) z).evalGround x =
      (atExpr p z).evalGround x + (atExpr q z).evalGround x := by
  induction p generalizing q with
  | nil =>
    change (atExpr q z).evalGround x = zero.evalGround x + (atExpr q z).evalGround x
    rw [ground_zero,zero_add]
  | cons a p ih =>
    cases q with
    | nil =>
      change (atExpr (a :: p) z).evalGround x = (atExpr (a :: p) z).evalGround x + zero.evalGround x
      rw [ground_zero,add_zero]
    | cons b q =>
      change (a.evalGround x + b.evalGround x) +
        z.evalGround x * (atExpr (plus p q) z).evalGround x =
        (a.evalGround x + z.evalGround x * (atExpr p z).evalGround x) +
        (b.evalGround x + z.evalGround x * (atExpr q z).evalGround x)
      rw [ih]
      ring

theorem atExpr_scale (c : Expr V) (p : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr (scale c p) z).evalGround x = c.evalGround x * (atExpr p z).evalGround x := by
  induction p with
  | nil =>
    change zero.evalGround x = c.evalGround x * zero.evalGround x
    rw [ground_zero,mul_zero]
  | cons a p ih =>
    change c.evalGround x * a.evalGround x +
      z.evalGround x * (atExpr (scale c p) z).evalGround x =
      c.evalGround x * (a.evalGround x + z.evalGround x * (atExpr p z).evalGround x)
    rw [ih]
    ring

theorem atExpr_linearMul (a : Expr V) (p : Poly V) (z : Expr V) (x : V → ℂ) :
    (atExpr (linearMul a p) z).evalGround x =
      (z.evalGround x - a.evalGround x) * (atExpr p z).evalGround x := by
  rw [linearMul,atExpr_plus,atExpr_scale]
  change zero.evalGround x + z.evalGround x * (atExpr p z).evalGround x +
    -(a.evalGround x) * (atExpr p z).evalGround x = _
  rw [ground_zero]
  ring

theorem atExpr_vanishing (p : List (Expr V)) (z : Expr V) (x : V → ℂ) :
    (atExpr (vanishing p) z).evalGround x =
      (p.map (fun a => z.evalGround x - a.evalGround x)).prod := by
  induction p with
  | nil =>
    change one.evalGround x + z.evalGround x * zero.evalGround x = 1
    rw [ground_one,ground_zero,mul_zero,add_zero]
  | cons a p ih =>
    rw [vanishing,atExpr_linearMul,ih,List.map_cons,List.prod_cons]

theorem atExpr_displacement (p : Poly V) (old : List (Expr V)) (z y w : Expr V) (x : V → ℂ) :
    (atExpr (displacement p old z y) w).evalGround x =
      (atExpr p w).evalGround x +
        ((y.evalGround x - (atExpr p z).evalGround x) /
          (old.map (fun a => z.evalGround x - a.evalGround x)).prod) *
            (old.map (fun a => w.evalGround x - a.evalGround x)).prod := by
  unfold displacement
  rw [atExpr_plus,atExpr_scale]
  change (atExpr p w).evalGround x +
    ((y.evalGround x + -(atExpr p z).evalGround x) *
      ((atExpr (vanishing old) z).evalGround x)⁻¹) *
        (atExpr (vanishing old) w).evalGround x = _
  simp only [atExpr_vanishing, sub_eq_add_neg, div_eq_mul_inv]

end ExprPoly

end JSP000930.Negative
