import JSP000930FreshCenterBatches

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion

namespace ExprPoly

variable {V W : Type}

theorem plus_rename (f : V → W) (p q : Poly V) :
    (plus p q).map (Expr.rename f) = plus (p.map (Expr.rename f)) (q.map (Expr.rename f)) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => simp only [plus,List.map_cons,Expr.rename,ih]

theorem scale_rename (f : V → W) (p : Poly V) (t : Expr V) :
    (scale t p).map (Expr.rename f) = scale (t.rename f) (p.map (Expr.rename f)) := by
  simp only [scale,List.map_map,Function.comp_def,Expr.rename]

theorem vanishing_rename (f : V → W) (p : List (Expr V)) :
    (vanishing p).map (Expr.rename f) = vanishing (p.map (Expr.rename f)) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [vanishing,List.map_cons,linearMul,plus_rename,scale_rename,ih,zero,Expr.rename]

end ExprPoly

open ExprPoly

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def pinOnlyDenominator (l : Finset J) :
    Expr (Option {i : J // i ∈ l}) :=
  atExpr (vanishing (l.attach.toList.map (fun i => Expr.atom (some i)))) (.atom none)

def pinOnlyAtomMap (p : PolyTrace B J) : Option {i : J // i ∈ p.pins} → TraceAtoms p
  | none => newSiteAtom p
  | some i => siteAtom p i

def pinOnlyEnv (l : Finset J) (site : J → ComplexBits B) (z : J) :
    Option {i : J // i ∈ l} → ComplexBits B
  | none => site z
  | some i => site i.1

theorem pinOnlyDenominator_rename (p : PolyTrace B J) :
    (pinOnlyDenominator p.pins).rename (pinOnlyAtomMap p) = traceDenominator p := by
  unfold pinOnlyDenominator traceDenominator oldSiteAtoms
  rw [← atExpr_rename,vanishing_rename,List.map_map,List.map_map] <;> rfl

theorem traceDenominator_eval_pinOnly (p : PolyTrace B J)
    (site : J → ComplexBits B) (z : J) (x : ComplexBits B) :
    (traceDenominator p).eval (traceEnv p site z x) =
      (pinOnlyDenominator p.pins).eval (pinOnlyEnv p.pins site z) := by
  rw [← pinOnlyDenominator_rename,Expr.eval_rename]
  have h : traceEnv p site z x ∘ pinOnlyAtomMap p = pinOnlyEnv p.pins site z := by
    funext i
    cases i <;> rfl
  rw [h]

theorem pinOnlyDenominator_map (F : CompleteValueMap B C) (p : PolyTrace B J)
    (site : J → ComplexBits B) (site' : J → ComplexBits C) (z : J)
    (hS : ∀ j ∈ p.pins,(site j).map F = site' j)
    (hZ : (site z).map F = site' z) (x : ComplexBits B) (y : ComplexBits C) :
    (((traceDenominator p).eval (traceEnv p site z x)).map F) =
      (traceDenominator (p.map F)).eval (traceEnv (p.map F) site' z y) := by
  rw [traceDenominator_eval_pinOnly,traceDenominator_eval_pinOnly,Expr.eval_map]
  have h : (fun i => ((pinOnlyEnv p.pins site z) i).map F) = pinOnlyEnv p.pins site' z := by
    funext i
    cases i with
    | none => exact hZ
    | some i => exact hS _ i.2
  rw [h]
  rfl

theorem oldSiteAtoms_length_map (F : CompleteValueMap B C) (p : PolyTrace B J) :
    (oldSiteAtoms (p.map F)).length = (oldSiteAtoms p).length := by
  simp only [oldSiteAtoms,List.length_map,PolyTrace.map]

end JSP000930.Negative
