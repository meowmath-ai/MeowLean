import JSP000930SymbolicTraceCardinality

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {J : Type}

theorem pinAt_first_inj (p : SymbolicTrace J) :
    Function.Injective (fun i : PinNumber p => (pinAt p i).1) := by
  intro i j h
  have hi : i.val < (p.pins.map Prod.fst).length := by simpa only [List.length_map] using i.2
  have hj : j.val < (p.pins.map Prod.fst).length := by simpa only [List.length_map] using j.2
  apply Fin.ext
  apply p.pins_unique.eq_of_getElem_eq hi hj
  simpa only [List.getElem_map, pinAt] using h

theorem mem_symbolicIndices (p : SymbolicTrace J) (i : PinNumber p) :
    i ∈ symbolicIndices p := List.mem_ofFn.mpr ⟨i,rfl⟩

theorem symbolicIndices_nodup (p : SymbolicTrace J) : (symbolicIndices p).Nodup := by
  unfold symbolicIndices
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj h
  simp only [List.getElem_ofFn,id_eq] at h
  exact congrArg Fin.val h

theorem mem_symbolicOtherSites (p : SymbolicTrace J) (i : PinNumber p) (s : SymbolIndex p) :
    s ∈ symbolicOtherSites p i ↔ ∃ j : PinNumber p, j ≠ i ∧ Sum.inl j = s := by
  unfold symbolicOtherSites
  constructor
  · intro hs
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hs
    exact ⟨k,decide_eq_true_iff.mp (List.mem_filter.mp hk).2,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact List.mem_map.mpr ⟨k,List.mem_filter.mpr ⟨mem_symbolicIndices p k,
      decide_eq_true_iff.mpr hk⟩,rfl⟩

theorem symbolicVanish_ground (p : SymbolicTrace J) (i : PinNumber p)
    (z : Expr (SymbolIndex p)) (w : SymbolIndex p → ℂ) :
    (atExpr (symbolicVanish p i) z).evalGround w =
      ((symbolicOtherSites p i).map (fun s => z.evalGround w - w s)).prod := by
  unfold symbolicVanish
  rw [atExpr_vanishing]
  rw [List.map_map]
  rfl

theorem symbolicCorrection_ground (p : SymbolicTrace J) (i : PinNumber p)
    (z : Expr (SymbolIndex p)) (w : SymbolIndex p → ℂ) :
    (atExpr (symbolicCorrection p i) z).evalGround w =
      ((w (Sum.inr i) - (atExpr (seedExpr p) (.atom (Sum.inl i))).evalGround w) /
        ((symbolicOtherSites p i).map (fun s => w (Sum.inl i) - w s)).prod) *
          ((symbolicOtherSites p i).map (fun s => z.evalGround w - w s)).prod := by
  unfold symbolicCorrection
  rw [atExpr_scale]
  change ((w (Sum.inr i) + -(atExpr (seedExpr p) (.atom (Sum.inl i))).evalGround w) *
    ((atExpr (symbolicVanish p i) (.atom (Sum.inl i))).evalGround w)⁻¹) *
      (atExpr (symbolicVanish p i) z).evalGround w = _
  simp only [symbolicVanish_ground, Expr.evalGround, sub_eq_add_neg, div_eq_mul_inv]

private theorem eval_foldr_plus {V K : Type} (P : K → ExprPoly.Poly V) (l : List K)
    (z : Expr V) (w : V → ℂ) :
    (atExpr (l.foldr (fun i a => plus (P i) a) []) z).evalGround w =
      (l.map (fun i => (atExpr (P i) z).evalGround w)).sum := by
  induction l with
  | nil => exact ground_zero w
  | cons a l ih =>
    change (atExpr (plus (P a) (l.foldr (fun i r => plus (P i) r) [])) z).evalGround w =
      (atExpr (P a) z).evalGround w + _
    rw [atExpr_plus,ih]
    rfl

theorem symbolicCoefficients_ground (p : SymbolicTrace J) (z : Expr (SymbolIndex p))
    (w : SymbolIndex p → ℂ) :
    (atExpr (symbolicCoefficients p) z).evalGround w =
      (atExpr (seedExpr p) z).evalGround w +
        ((symbolicIndices p).map (fun i => (atExpr (symbolicCorrection p i) z).evalGround w)).sum := by
  unfold symbolicCoefficients
  rw [atExpr_plus,eval_foldr_plus]

private theorem product_difference_zero {V : Type} (w : V → ℂ) (x : V)
    (l : List V) (hx : x ∈ l) : (l.map (fun i => w x - w i)).prod = 0 := by
  induction l with
  | nil => exact (List.not_mem_nil hx).elim
  | cons a l ih =>
    rcases List.mem_cons.mp hx with h|h
    · subst a
      simp only [List.map_cons,List.prod_cons,sub_self,zero_mul]
    · simp only [List.map_cons,List.prod_cons,ih h,mul_zero]

private theorem sum_only_one {V : Type} [DecidableEq V] (l : List V) (hN : l.Nodup)
    (x : V) (f : V → ℂ) (h : ∀ i ∈ l, i ≠ x → f i = 0) :
    (l.map f).sum = if x ∈ l then f x else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl := ih (List.nodup_cons.mp hN).2
      (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases ha : a = x
    · subst a
      have hx : x ∉ l := (List.nodup_cons.mp hN).1
      simp only [List.map_cons,List.sum_cons,hl,ite_eq_right hx,add_zero,List.mem_cons_self,ite_true]
    · have hA := h a List.mem_cons_self ha
      simp only [List.map_cons,List.sum_cons,hA,zero_add,hl,List.mem_cons,
        show x ≠ a from Ne.symm ha,false_or]

theorem symbolic_ground_pin (p : SymbolicTrace J) (i : PinNumber p)
    (w : SymbolIndex p → ℂ)
    (hApart : ∀ s ∈ symbolicOtherSites p i, w (Sum.inl i) ≠ w s) :
    (atExpr (symbolicCoefficients p) (.atom (Sum.inl i))).evalGround w = w (Sum.inr i) := by
  have hOnly (j : PinNumber p) (hj : j ∈ symbolicIndices p) (hji : j ≠ i) :
      (atExpr (symbolicCorrection p j) (.atom (Sum.inl i))).evalGround w = 0 := by
    rw [symbolicCorrection_ground]
    have hs : Sum.inl i ∈ symbolicOtherSites p j :=
      (mem_symbolicOtherSites p j _).mpr ⟨i,Ne.symm hji,rfl⟩
    simp only [Expr.evalGround,product_difference_zero w (Sum.inl i) _ hs,mul_zero]
  rw [symbolicCoefficients_ground,sum_only_one _ (symbolicIndices_nodup p) i _ hOnly,
    ite_eq_left (mem_symbolicIndices p i),symbolicCorrection_ground]
  simp only [Expr.evalGround]
  letI : Nonempty (SymbolIndex p) := ⟨Sum.inl i⟩
  rw [div_mul_cancel₀ _ (scalar_factors_ne_zero w (Sum.inl i) _ hApart)]
  ring

end JSP000930.Negative
