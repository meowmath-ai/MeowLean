import JSP000930SymbolicNamedPinValidity
import JSP000930SeedHornerBound

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B V W : Type} [NontrivialCompleteBooleanAlgebra B]

def Expr.rename (f : V → W) : Expr V → Expr W
  | .atom i => .atom (f i)
  | .num a b => .num a b
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)
  | .neg a => .neg (a.rename f)
  | .inv a => .inv (a.rename f)

theorem Expr.eval_rename (f : V → W) (u : W → ComplexBits B) (a : Expr V) :
    (a.rename f).eval u = a.eval (u ∘ f) := by
  induction a <;> simp_all only [Expr.rename,Expr.eval,Function.comp_apply]

theorem Expr.evalGround_rename (f : V → W) (u : W → ℂ) (a : Expr V) :
    (a.rename f).evalGround u = a.evalGround (u ∘ f) := by
  induction a <;> simp_all only [Expr.rename,Expr.evalGround,Function.comp_apply]

theorem Expr.denominators_rename (f : V → W) (a : Expr V) :
    (a.rename f).denominators = a.denominators.map (Expr.rename f) := by
  induction a <;> simp_all only [Expr.rename,Expr.denominators,List.map_nil,
    List.map_cons,List.map_append]

theorem Expr.safe_rename (f : V → W) (u : W → ComplexBits B) (a : Expr V)
    (m : B) (ha : a.Safe (u ∘ f) m) : (a.rename f).Safe u m := by
  intro d hd
  rw [Expr.denominators_rename] at hd
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
  rw [Expr.eval_rename]
  exact ha c hc

namespace ExprPoly

theorem atExpr_rename (f : V → W) (p : Poly V) (z : Expr V) :
    atExpr (p.map (Expr.rename f)) (z.rename f) = (atExpr p z).rename f := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change Expr.add (a.rename f) (Expr.mul (z.rename f) (atExpr (p.map (Expr.rename f)) (z.rename f))) =
      Expr.add (a.rename f) (Expr.mul (z.rename f) ((atExpr p z).rename f))
    rw [ih]

theorem scalarPolynomialEval_map_seed (l : List (ℚ × ℚ)) (z : ℂ) (w : V → ℂ) :
    scalarPolynomialEval ((l.map (fun r => Expr.num r.1 r.2)).map (Expr.evalGround w)) z =
      scalarPolynomialEval (l.map gaussianRat) z := by
  congr 1
  rw [List.map_map] <;> rfl

theorem mixedPolynomialEval_map_seed (l : List (ℚ × ℚ)) (z : ComplexBits B)
    (w : V → ComplexBits B) :
    mixedPolynomialEval ((l.map (fun r => Expr.num r.1 r.2)).map (Expr.eval w)) z =
      mixedPolynomialEval (l.map (fun r => ComplexBits.checked (gaussianRat r))) z := by
  congr 1
  rw [List.map_map] <;> rfl

end ExprPoly

end JSP000930.Negative
