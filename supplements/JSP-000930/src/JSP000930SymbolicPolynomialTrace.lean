import JSP000930GenericFineTraceCovers

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

structure SymbolicTrace (J : Type) where
  seed : List (ℚ × ℚ)
  pins : List (J × ℕ)
  radius : ℕ
  budget : ℚ
  budget_pos : 0 < budget
  pins_unique : (pins.map Prod.fst).Nodup

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

abbrev PinNumber (p : SymbolicTrace J) := Fin p.pins.length

abbrev SymbolIndex (p : SymbolicTrace J) := PinNumber p ⊕ PinNumber p

def pinAt (p : SymbolicTrace J) (j : PinNumber p) : J × ℕ :=
  p.pins[j.val]'j.2

def symbolVal (p : SymbolicTrace J) (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) : SymbolIndex p → ComplexBits B
  | .inl i => site (pinAt p i).1
  | .inr i => H (pinAt p i).1 (pinAt p i).2

theorem symbolVal_map (F : JSP000933.BooleanCompletion.CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (p : SymbolicTrace J) :
    (fun i => (symbolVal p site H i).map F) =
      symbolVal p (fun i => (site i).map F) (fun i n => (H i n).map F) := by
  funext i
  cases i <;> rfl

def seedExpr (p : SymbolicTrace J) : ExprPoly.Poly (SymbolIndex p) :=
  p.seed.map (fun v => Expr.num v.1 v.2)

def symbolicIndices (p : SymbolicTrace J) : List (PinNumber p) :=
  List.ofFn id

def symbolicOtherSites (p : SymbolicTrace J) (x : PinNumber p) : List (SymbolIndex p) :=
  ((symbolicIndices p).filter (fun t => decide (t ≠ x))).map Sum.inl

def symbolicVanish (p : SymbolicTrace J) (x : PinNumber p) :
    ExprPoly.Poly (SymbolIndex p) :=
  ExprPoly.vanishing ((symbolicOtherSites p x).map Expr.atom)

def symbolicCorrection (p : SymbolicTrace J) (i : PinNumber p) :
    ExprPoly.Poly (SymbolIndex p) :=
  let z := Expr.atom (Sum.inl i)
  let y := Expr.atom (Sum.inr i)
  let R := ExprPoly.atExpr (seedExpr p) z
  let D := ExprPoly.atExpr (symbolicVanish p i) z
  ExprPoly.scale (.mul (.add y (.neg R)) (.inv D)) (symbolicVanish p i)

def symbolicCoefficients (p : SymbolicTrace J) :
    ExprPoly.Poly (SymbolIndex p) :=
  ExprPoly.plus (seedExpr p) ((symbolicIndices p).foldr
    (fun i a => ExprPoly.plus (symbolicCorrection p i) a) [])

noncomputable def decodeSymbolicTrace (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : SymbolicTrace J) : PolyTrace B J := by
  classical
  exact ⟨(symbolicCoefficients p).map (Expr.eval (symbolVal p site H)),
    (p.pins.map Prod.fst).toFinset, p.radius, p.budget, p.budget_pos⟩

theorem decodeSymbolicTrace_map (F : JSP000933.BooleanCompletion.CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (p : SymbolicTrace J) :
    (decodeSymbolicTrace site H p).map F =
      decodeSymbolicTrace (fun i => (site i).map F) (fun i n => (H i n).map F) p := by
  have hh (e : Expr (SymbolIndex p)) : ((e.eval (symbolVal p site H)).map F) =
      e.eval (symbolVal p (fun i => (site i).map F) (fun i n => (H i n).map F)) := by
    rw [Expr.eval_map,symbolVal_map]
  unfold decodeSymbolicTrace PolyTrace.map
  rw [List.map_map]
  have hFunctions :
      ComplexBits.map F ∘ Expr.eval (symbolVal p site H) =
        Expr.eval (symbolVal p (fun i => (site i).map F) (fun i n => (H i n).map F)) := by
    funext e
    exact hh e
  rw [hFunctions]

end JSP000930.Negative
