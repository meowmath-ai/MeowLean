import JSP000930FiniteExpressionPolynomials

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

namespace ExprPoly

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B]

def CoeffSafe (u : V → ComplexBits B) (m : B) (p : Poly V) : Prop :=
  ∀ e ∈ p, e.Safe u m

private theorem safe_zero (u : V → ComplexBits B) (m : B) : (zero : Expr V).Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

private theorem safe_one (u : V → ComplexBits B) (m : B) : (one : Expr V).Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

theorem safe_add {u : V → ComplexBits B} {m : B} {a b : Expr V}
    (ha : a.Safe u m) (hb : b.Safe u m) : (a.add b).Safe u m := by
  intro d hd
  exact (List.mem_append.mp hd).elim (ha d) (hb d)

theorem safe_mul {u : V → ComplexBits B} {m : B} {a b : Expr V}
    (ha : a.Safe u m) (hb : b.Safe u m) : (a.mul b).Safe u m := by
  intro d hd
  exact (List.mem_append.mp hd).elim (ha d) (hb d)

theorem safe_neg {u : V → ComplexBits B} {m : B} {a : Expr V}
    (ha : a.Safe u m) : a.neg.Safe u m := ha

theorem safe_inv {u : V → ComplexBits B} {m : B} {a : Expr V}
    (ha : a.Safe u m) (hPos : m ≤ positiveCutValue (a.eval u).normSq) :
    a.inv.Safe u m := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl|hd
  · exact hPos
  · exact ha d hd

theorem coeffSafe_plus {u : V → ComplexBits B} {m : B} {p q : Poly V}
    (hp : CoeffSafe u m p) (hq : CoeffSafe u m q) : CoeffSafe u m (plus p q) := by
  induction p generalizing q with
  | nil => exact hq
  | cons a p ih =>
    cases q with
    | nil => exact hp
    | cons b q =>
      intro c hc
      change c ∈ Expr.add a b :: plus p q at hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact safe_add (hp a List.mem_cons_self) (hq b List.mem_cons_self)
      · exact ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))
          (fun d hd => hq d (List.mem_cons_of_mem _ hd)) c hc

theorem coeffSafe_scale {u : V → ComplexBits B} {m : B} {c : Expr V} {p : Poly V}
    (hc : c.Safe u m) (hp : CoeffSafe u m p) : CoeffSafe u m (scale c p) := by
  intro d hd
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
  exact safe_mul hc (hp a ha)

theorem coeffSafe_linearMul {u : V → ComplexBits B} {m : B} {a : Expr V} {p : Poly V}
    (ha : a.Safe u m) (hp : CoeffSafe u m p) : CoeffSafe u m (linearMul a p) := by
  apply coeffSafe_plus ?_ (coeffSafe_scale (safe_neg ha) hp)
  intro d hd
  rcases List.mem_cons.mp hd with rfl|hd
  · exact safe_zero u m
  · exact hp d hd

theorem coeffSafe_vanishing {u : V → ComplexBits B} {m : B}
    {old : List (Expr V)} (ho : CoeffSafe u m old) : CoeffSafe u m (vanishing old) := by
  induction old with
  | nil =>
    intro d hd
    have hd' : d = one := List.mem_singleton.mp hd
    subst d
    exact safe_one u m
  | cons a t ih =>
    exact coeffSafe_linearMul (ho a List.mem_cons_self)
      (ih (fun d hd => ho d (List.mem_cons_of_mem _ hd)))

theorem atExpr_safe {u : V → ComplexBits B} {m : B}
    {p : Poly V} {z : Expr V} (hp : CoeffSafe u m p) (hz : z.Safe u m) :
    (atExpr p z).Safe u m := by
  induction p with
  | nil => exact safe_zero u m
  | cons a p ih =>
    exact safe_add (hp a List.mem_cons_self)
      (safe_mul hz (ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))))

theorem coeffSafe_displacement {u : V → ComplexBits B} {m : B}
    {p : Poly V} {old : List (Expr V)} {z y : Expr V}
    (hp : CoeffSafe u m p) (hOld : CoeffSafe u m old)
    (hz : z.Safe u m) (hy : y.Safe u m)
    (hDen : m ≤ positiveCutValue ((atExpr (vanishing old) z).eval u).normSq) :
    CoeffSafe u m (displacement p old z y) := by
  have hVan := coeffSafe_vanishing hOld
  have hInv := safe_inv (atExpr_safe hVan hz) hDen
  have hDiff := safe_add hy (safe_neg (atExpr_safe hp hz))
  exact coeffSafe_plus hp (coeffSafe_scale (safe_mul hDiff hInv) hVan)

theorem atExpr_eval (u : V → ComplexBits B) (p : Poly V) (z : Expr V) :
    (atExpr p z).eval u = mixedPolynomialEval (p.map (Expr.eval u)) (z.eval u) := by
  induction p with
  | nil =>
    change (⟨checkedRealBits (((0 : ℚ) : ℝ)),checkedRealBits (((0 : ℚ) : ℝ))⟩ : ComplexBits B) =
      ⟨checkedRealBits (((0 : ℕ) : ℝ)),checkedRealBits 0⟩
    simp only [Rat.cast_zero,Nat.cast_zero]
  | cons a p ih =>
    change (a.eval u).add ((z.eval u).mul ((atExpr p z).eval u)) =
      (a.eval u).add ((z.eval u).mul (mixedPolynomialEval (p.map (Expr.eval u)) (z.eval u)))
    rw [ih]

end ExprPoly

end JSP000930.Negative
