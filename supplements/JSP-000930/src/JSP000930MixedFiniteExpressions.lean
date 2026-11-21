import JSP000930NamedComplexInverse

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion

inductive Expr (V : Type) where
  | atom : V → Expr V
  | num : ℚ → ℚ → Expr V
  | add : Expr V → Expr V → Expr V
  | mul : Expr V → Expr V → Expr V
  | neg : Expr V → Expr V
  | inv : Expr V → Expr V

variable {B C V : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def Expr.eval (u : V → ComplexBits B) : Expr V → ComplexBits B
  | .atom i => u i
  | .num a b => ComplexBits.checked ⟨(a : ℝ),(b : ℝ)⟩
  | .add a b => (a.eval u).add (b.eval u)
  | .mul a b => (a.eval u).mul (b.eval u)
  | .neg a => (a.eval u).neg
  | .inv a => (a.eval u).inv

noncomputable def Expr.evalGround (u : V → ℂ) : Expr V → ℂ
  | .atom i => u i
  | .num a b => ⟨(a : ℝ),(b : ℝ)⟩
  | .add a b => a.evalGround u + b.evalGround u
  | .mul a b => a.evalGround u * b.evalGround u
  | .neg a => -(a.evalGround u)
  | .inv a => (a.evalGround u)⁻¹

def Expr.denominators : Expr V → List (Expr V)
  | .atom _ => []
  | .num _ _ => []
  | .add a b => a.denominators ++ b.denominators
  | .mul a b => a.denominators ++ b.denominators
  | .neg a => a.denominators
  | .inv a => a :: a.denominators

def Expr.Safe (u : V → ComplexBits B) (m : B) (e : Expr V) : Prop :=
  ∀ d ∈ e.denominators, m ≤ positiveCutValue (d.eval u).normSq

theorem Expr.safe_mono {u : V → ComplexBits B} {m k : B} {e : Expr V}
    (h : e.Safe u m) (hk : k ≤ m) : e.Safe u k :=
  fun d hd => hk.trans (h d hd)

theorem Expr.eval_cutOn (u : V → ComplexBits B) (m : B) (e : Expr V)
    (hu : ∀ i, (u i).CutOn m) (h : e.Safe u m) : (e.eval u).CutOn m := by
  induction e with
  | atom i => exact hu i
  | num a b => exact ComplexBits.checked_cutOn _ m
  | add a b ia ib =>
    exact ComplexBits.add_cutOn
      (ia (fun d hd => h d (List.mem_append_left _ hd)))
      (ib (fun d hd => h d (List.mem_append_right _ hd)))
  | mul a b ia ib =>
    exact ComplexBits.mul_cutOn
      (ia (fun d hd => h d (List.mem_append_left _ hd)))
      (ib (fun d hd => h d (List.mem_append_right _ hd)))
  | neg a ia => exact ComplexBits.neg_cutOn (ia h)
  | inv a ia =>
    exact ComplexBits.inv_cutOn
      (ia (fun d hd => h d (List.mem_cons_of_mem _ hd))) (h a List.mem_cons_self)

theorem Expr.eval_map (F : CompleteValueMap B C) (u : V → ComplexBits B) (e : Expr V) :
    (e.eval u).map F = e.eval (fun i => (u i).map F) := by
  induction e with
  | atom i => rfl
  | num a b => exact ComplexBits.map_checked F _
  | add a b ia ib => simp only [Expr.eval, ComplexBits.map_add, ia, ib]
  | mul a b ia ib => simp only [Expr.eval, ComplexBits.map_mul, ia, ib]
  | neg a ia => simp only [Expr.eval, ComplexBits.map_neg, ia]
  | inv a ia => simp only [Expr.eval, ComplexBits.map_inv, ia]

theorem Expr.safe_map (F : CompleteValueMap B C) {u : V → ComplexBits B}
    {m : B} {e : Expr V} (h : e.Safe u m) :
    e.Safe (fun i => (u i).map F) (F.toFun m) := by
  intro d hd
  simpa only [map_positiveCutValue, ComplexBits.map_normSq, Expr.eval_map] using
    F.monotone (h d hd)

end JSP000930.Negative
