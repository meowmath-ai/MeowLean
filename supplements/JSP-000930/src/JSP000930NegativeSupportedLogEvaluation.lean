import JSP000930NegativeSupportedLogChart

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] {A : J → Prop}

private def uniformIndices930 (n : ℕ) : List (Fin n) := List.ofFn id
private def uniformSeed930 (n : ℕ) (seed : List (ℚ × ℚ)) : ExprPoly.Poly (Fin n ⊕ Fin n) :=
  seed.map (fun c => Expr.num c.1 c.2)
private def uniformVanish930 (n : ℕ) (i : Fin n) : ExprPoly.Poly (Fin n ⊕ Fin n) :=
  vanishing (((uniformIndices930 n).filter (fun t => decide (t ≠ i))).map
    (fun j => Expr.atom (Sum.inl j)))
private def uniformCorrection930 (n : ℕ) (seed : List (ℚ × ℚ)) (i : Fin n) : ExprPoly.Poly (Fin n ⊕ Fin n) :=
  let z := Expr.atom (Sum.inl i)
  let y := Expr.atom (Sum.inr i)
  let R := atExpr (uniformSeed930 n seed) z
  let D := atExpr (uniformVanish930 n i) z
  scale (.mul (.add y (.neg R)) (.inv D)) (uniformVanish930 n i)
private def uniformCoeffs930 (n : ℕ) (seed : List (ℚ × ℚ)) : ExprPoly.Poly (Fin n ⊕ Fin n) :=
  plus (uniformSeed930 n seed) ((uniformIndices930 n).foldr
    (fun i a => plus (uniformCorrection930 n seed i) a) [])

private theorem symbolicCoefficients_uniform930 (p : SymbolicTrace J) :
    symbolicCoefficients p = uniformCoeffs930 p.pins.length p.seed := by
  simp only [symbolicCoefficients,uniformCoeffs930,seedExpr,uniformSeed930,symbolicIndices,
    uniformIndices930,symbolicCorrection,uniformCorrection930,symbolicVanish,
    uniformVanish930,symbolicOtherSites,List.map_map]
  rfl

private def castSymbol930 {n m : ℕ} (h : n=m) : (Fin n ⊕ Fin n) → (Fin m ⊕ Fin m)
  | .inl i => .inl (Fin.cast h i)
  | .inr i => .inr (Fin.cast h i)

private theorem uniformCoeffs_congr930 {n m : ℕ} (hl : n=m) (seed : List (ℚ × ℚ))
    (u : Fin n ⊕ Fin n → ComplexBits B) (v : Fin m ⊕ Fin m → ComplexBits B)
    (he : ∀ i,u i = v (castSymbol930 hl i)) :
    (uniformCoeffs930 n seed).map (Expr.eval u) =
      (uniformCoeffs930 m seed).map (Expr.eval v) := by
  subst m
  rw [show u=v from funext (fun i => by cases i <;> exact he _)]

abbrev allowedSite930 (s : J → ComplexBits B) : AllowedPin A → ComplexBits B := fun i => s i.val
abbrev allowedPalette930 (H : J → ℕ → ComplexBits B) : AllowedPin A → ℕ → ComplexBits B := fun i => H i.val
noncomputable abbrev highDecode930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) := decodeSymbolicTrace site H (raiseSymbolicLog p)
noncomputable abbrev lowDecode930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) := decodeSymbolicTrace (allowedSite930 site) (allowedPalette930 H) p

theorem raise_decode_coeff930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) :
    (highDecode930 site H p).coeff = (lowDecode930 site H p).coeff := by
  change (symbolicCoefficients (raiseSymbolicLog p)).map (Expr.eval (symbolVal (raiseSymbolicLog p) site H)) =
    (symbolicCoefficients p).map (Expr.eval (symbolVal p (allowedSite930 site) (allowedPalette930 H)))
  rw [symbolicCoefficients_uniform930,symbolicCoefficients_uniform930]
  apply uniformCoeffs_congr930 (show (raiseSymbolicLog p).pins.length = p.pins.length from List.length_map forgetPin930)
  intro i
  rcases i with i|i
  · simp only [castSymbol930,symbolVal,allowedSite930,pinAt,raiseSymbolicLog,
      List.getElem_map,forgetPin930]
    rfl
  · simp only [castSymbol930,symbolVal,allowedPalette930,pinAt,raiseSymbolicLog,
      List.getElem_map,forgetPin930]
    rfl

theorem raise_decode_mem930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) (j : J) :
    j ∈ (highDecode930 site H p).pins ↔
      ∃ i : AllowedPin A,i ∈ (lowDecode930 site H p).pins ∧ i.val=j := by
  classical
  simp only [highDecode930,lowDecode930,decodeSymbolicTrace,raiseSymbolicLog,List.mem_toFinset,List.map_map,List.mem_map,Function.comp_apply]
  constructor
  · rintro ⟨v,hv,he⟩
    exact ⟨v.1,⟨v,hv,rfl⟩,he⟩
  · rintro ⟨i,⟨v,hv,hvi⟩,he⟩
    exact ⟨v,hv,(congrArg Subtype.val hvi).trans he⟩

theorem raise_decode_pin_iff930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) (i : AllowedPin A) :
    i.val ∈ (highDecode930 site H p).pins ↔ i ∈ (lowDecode930 site H p).pins := by
  rw [raise_decode_mem930]
  constructor
  · rintro ⟨j,hj,hji⟩
    exact Subtype.ext hji ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem raise_eval930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace (AllowedPin A)) (z : ComplexBits B) :
    (highDecode930 site H p).eval z = (lowDecode930 site H p).eval z := by
  unfold PolyTrace.eval
  rw [raise_decode_coeff930 site H p]

end JSP000930.Negative
