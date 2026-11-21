import JSP000930FiniteNormBounds

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B]

def Expr.Only (P : V → Prop) : Expr V → Prop
  | .atom i => P i
  | .num .. => True
  | .add a b => a.Only P ∧ b.Only P
  | .mul a b => a.Only P ∧ b.Only P
  | .neg a => a.Only P
  | .inv a => a.Only P

theorem Expr.eval_eq_of_only {P : V → Prop} (e : Expr V)
    {u v : V → ComplexBits B} (he : e.Only P) (h : ∀ i, P i → u i = v i) :
    e.eval u = e.eval v := by
  induction e with
  | atom i => exact h i he
  | num a b => rfl
  | add a b ia ib => simp only [Expr.eval, ia he.1, ib he.2]
  | mul a b ia ib => simp only [Expr.eval, ia he.1, ib he.2]
  | neg a ia => simp only [Expr.eval, ia he]
  | inv a ia => simp only [Expr.eval, ia he]

namespace ExprPoly

def CoeffOnly (P : V → Prop) (p : Poly V) : Prop :=
  ∀ e ∈ p, e.Only P

theorem atExpr_only {P : V → Prop} {p : Poly V} {z : Expr V}
    (hp : CoeffOnly P p) (hz : z.Only P) : (atExpr p z).Only P := by
  induction p with
  | nil => exact True.intro
  | cons a p ih =>
    exact ⟨hp a List.mem_cons_self, hz,
      ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))⟩

theorem coeffOnly_plus {P : V → Prop} {p q : Poly V}
    (hp : CoeffOnly P p) (hq : CoeffOnly P q) : CoeffOnly P (plus p q) := by
  induction p generalizing q with
  | nil => exact hq
  | cons a p ih =>
    cases q with
    | nil => exact hp
    | cons b q =>
      intro c hc
      change c ∈ Expr.add a b :: plus p q at hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact ⟨hp a List.mem_cons_self,hq b List.mem_cons_self⟩
      · exact ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))
          (fun d hd => hq d (List.mem_cons_of_mem _ hd)) c hc

theorem coeffOnly_scale {P : V → Prop} {p : Poly V} {c : Expr V}
    (hp : CoeffOnly P p) (hc : c.Only P) : CoeffOnly P (scale c p) := by
  intro d hd
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
  exact ⟨hc,hp a ha⟩

theorem coeffOnly_vanishing {P : V → Prop} {p : Poly V}
    (hp : CoeffOnly P p) : CoeffOnly P (vanishing p) := by
  induction p with
  | nil =>
    intro e he
    have he' : e = one := List.mem_singleton.mp he
    subst e
    exact True.intro
  | cons a p ih =>
    have hP := ih (fun e he => hp e (List.mem_cons_of_mem _ he))
    change CoeffOnly P (plus (zero :: vanishing p) (scale a.neg (vanishing p)))
    have ha : a.neg.Only P := hp a List.mem_cons_self
    apply coeffOnly_plus ?_ (coeffOnly_scale hP ha)
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact True.intro
    · exact hP e he

end ExprPoly

end JSP000930.Negative
