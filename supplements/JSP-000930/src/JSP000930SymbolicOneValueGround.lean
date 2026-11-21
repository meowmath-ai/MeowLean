import JSP000930SymbolicDisplacementGround

namespace JSP000930.Negative

open ExprPoly

variable {J : Type}

theorem seedEvalGround_independent (p : SymbolicTrace J)
    (u v : SymbolIndex p → ℂ) (z z' : Expr (SymbolIndex p))
    (hZ : z.evalGround u = z'.evalGround v) :
    (atExpr (seedExpr p) z).evalGround u =
      (atExpr (seedExpr p) z').evalGround v := by
  rw [ground_atExpr,ground_atExpr,hZ]
  unfold seedExpr
  rw [scalarPolynomialEval_map_seed,scalarPolynomialEval_map_seed]

private theorem same_list_diff_meet_p108 {I : Type} (l : List I) (F G : I → ℂ) :
    (l.map F).sum - (l.map G).sum = (l.map (fun i => F i - G i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,← ih]
    abel

private theorem sum_only_one_p108 {V : Type} [DecidableEq V] (l : List V) (hN : l.Nodup)
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

theorem symbolic_ground_one_value_shift (p : SymbolicTrace J) (i : PinNumber p)
    (z : Expr (SymbolIndex p)) (u v : SymbolIndex p → ℂ)
    (hZ : z.evalGround u = z.evalGround v)
    (hSite : ∀ j : PinNumber p,u (.inl j) = v (.inl j))
    (hVal : ∀ j : PinNumber p,j ≠ i → u (.inr j) = v (.inr j)) :
    (atExpr (symbolicCoefficients p) z).evalGround v -
      (atExpr (symbolicCoefficients p) z).evalGround u =
    ((v (.inr i)-u (.inr i)) /
      ((symbolicOtherSites p i).map (fun s => v (.inl i)-v s)).prod) *
      ((symbolicOtherSites p i).map (fun s => z.evalGround v-v s)).prod := by
  let f (j : PinNumber p) := (atExpr (symbolicCorrection p j) z).evalGround v
  let g (j : PinNumber p) := (atExpr (symbolicCorrection p j) z).evalGround u
  let D (j : PinNumber p) := ((symbolicOtherSites p j).map (fun s => v (.inl j)-v s)).prod
  let N (j : PinNumber p) := ((symbolicOtherSites p j).map (fun s => z.evalGround v-v s)).prod
  have hPart (j : PinNumber p) :
      f j - g j = ((v (.inr j)-u (.inr j)) / D j)*(N j) := by
    have hs (s : SymbolIndex p) (hs : s ∈ symbolicOtherSites p j) : u s = v s := by
      obtain ⟨k,_,rfl⟩ := (mem_symbolicOtherSites p j s).mp hs
      exact hSite k
    have hD : ((symbolicOtherSites p j).map (fun s => u (.inl j)-u s)).prod = D j := by
      congr 1
      apply List.map_congr_left
      intro s hm
      rw [hSite j,hs s hm]
    have hN : ((symbolicOtherSites p j).map (fun s => z.evalGround u-u s)).prod = N j := by
      congr 1
      apply List.map_congr_left
      intro s hm
      rw [hZ,hs s hm]
    have hSeed := seedEvalGround_independent p u v (.atom (.inl j)) (.atom (.inl j)) (hSite j)
    unfold f g
    rw [symbolicCorrection_ground,symbolicCorrection_ground,hD,hN,hSeed]
    simp only [div_eq_mul_inv]
    ring
  rw [symbolicCoefficients_ground,symbolicCoefficients_ground]
  have hS := seedEvalGround_independent p u v z z hZ
  change (atExpr (seedExpr p) z).evalGround v + ((symbolicIndices p).map f).sum -
    ((atExpr (seedExpr p) z).evalGround u + ((symbolicIndices p).map g).sum) = _
  rw [hS,show (atExpr (seedExpr p) z).evalGround v + ((symbolicIndices p).map f).sum -
      ((atExpr (seedExpr p) z).evalGround v + ((symbolicIndices p).map g).sum) =
      ((symbolicIndices p).map f).sum - ((symbolicIndices p).map g).sum by abel,
    same_list_diff_meet_p108]
  suffices hn : (((symbolicIndices p).map (fun j => f j - g j)).sum) = f i - g i by
    rw [hn,hPart] <;> rfl
  have h := sum_only_one_p108 (symbolicIndices p) (symbolicIndices_nodup p) i
    (fun j => f j - g j) (by
      intro j hj hn
      rw [hPart,hVal j hn,sub_self,zero_div,zero_mul])
  simpa only [ite_eq_left (mem_symbolicIndices p i)] using h

theorem symbolic_anchor_product_bound (p : SymbolicTrace J) (i : PinNumber p)
    (z : Expr (SymbolIndex p)) (w : SymbolIndex p → ℂ) (L : ℝ)
    (hL : 1 ≤ L) (hZ : ‖z.evalGround w‖ ≤ L)
    (hS : ∀ j : PinNumber p,‖w (.inl j)‖ ≤ L) :
    ‖((symbolicOtherSites p i).map (fun a => z.evalGround w - w a)).prod‖ ≤
      (L+L)^p.pins.length := by
  let l := symbolicOtherSites p i
  let u : Option (SymbolIndex p) → ℂ
    | none => z.evalGround w
    | some a => w a
  have hNorms : ∀ a ∈ l.map some, ‖u a‖ ≤ L := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,rfl⟩ := (mem_symbolicOtherSites p i b).mp hb
    exact hS j
  have hp := scalar_anchor_bound u (l.map some) none (zero_le_one.trans hL)
    (zero_le_one.trans hL) hZ hNorms
  simp only [List.map_map,List.length_map,Function.comp_apply,u] at hp
  refine hp.trans ?_
  apply pow_le_pow_right₀ (by linarith)
  exact symbolicOtherSites_length_le p i

end JSP000930.Negative
